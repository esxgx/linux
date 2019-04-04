// SPDX-License-Identifier: GPL-2.0
/*
 * linux/drivers/staging/erofs/utils.c
 *
 * Copyright (C) 2018 HUAWEI, Inc.
 *             http://www.huawei.com/
 * Created by Gao Xiang <gaoxiang25@huawei.com>
 *
 * This file is subject to the terms and conditions of the GNU General Public
 * License.  See the file COPYING in the main directory of the Linux
 * distribution for more details.
 */

#include "internal.h"
#include <linux/module.h>
#include <linux/mempool.h>
#include <linux/cpu.h>
#include <linux/cpuhotplug.h>
#include <linux/pagevec.h>

static mempool_t *erofs_bounce_page_pool;
static unsigned int bounce_max_rsvpages = 32;

static int set_bounce_rsvpages(const char *val, const struct kernel_param *kp)
{
	int ret = param_set_uint(val, kp);

	if (ret)
		return ret;

	if (!bounce_max_rsvpages)
		mempool_destroy(erofs_bounce_page_pool);
	else
		mempool_resize(erofs_bounce_page_pool, bounce_max_rsvpages);
	return 0;
}

module_param_call(num_rsvpages, set_bounce_rsvpages,
		  param_get_uint, &bounce_max_rsvpages, 0644);
__MODULE_PARM_TYPE(num_rsvpages, "uint");
MODULE_PARM_DESC(num_rsvpages,
 "Number of preallocated bounce pages which can be used temporarily");

int erofs_bounce_pool_init(void)
{
	if (!bounce_max_rsvpages)
		return 0;

	erofs_bounce_page_pool =
		mempool_create_page_pool(bounce_max_rsvpages, 0);
	if (!erofs_bounce_page_pool)
		return -ENOMEM;
	return 0;
}

void erofs_bounce_pool_exit(void)
{
	if (!erofs_bounce_page_pool)
		return;

	mempool_destroy(erofs_bounce_page_pool);
}

struct page *erofs_allocpage(struct list_head *pool,
			     gfp_t gfp, bool bounce, bool nofail)
{
	struct page *page;

	if (!list_empty(pool)) {
		page = lru_to_page(pool);
		list_del(&page->lru);
		return page;
	}
	if (bounce && erofs_bounce_page_pool) {
		/*
		 * Don't sleep if no page in mempool since decompressor
		 * can allocate multiple bounce pages at once and
		 * it will cause unexpected blockings.
		 */
		page = mempool_alloc(erofs_bounce_page_pool,
				     gfp & ~__GFP_DIRECT_RECLAIM);
		if (page)
			return page;
	}
	return alloc_pages(gfp | (nofail ? __GFP_NOFAIL : 0), 0);
}

void erofs_putpage(struct page *page)
{
	if (erofs_bounce_page_pool &&
	    page_ref_count(page) == 1 && !page->mapping) {
		mempool_free(page, erofs_bounce_page_pool);
		return;
	}
	put_page(page);
}

void erofs_put_pages_list(struct list_head *pool)
{
	if (!erofs_bounce_page_pool) {
		put_pages_list(pool);
		return;
	}

	while (!list_empty(pool)) {
		struct page *const page = lru_to_page(pool);

		list_del(&page->lru);
		DBG_BUGON(page_ref_count(page) != 1);
		page->mapping = NULL;
		mempool_free(page, erofs_bounce_page_pool);
	}
}

struct erofs_pcpu_vma {
	/* vm area for mapping object that span pages */
	struct vm_struct *vm;

	unsigned int nr_pages;
};

static const unsigned int percpu_vma_maxpages[EROFS_NR_PERCPU_VMA] = { 32 };

/* mainly used to protect vma_maxpages consistent with vm */
static rwlock_t percpu_vmalock[EROFS_NR_PERCPU_VMA] = {__RW_LOCK_UNLOCKED(0)};

static DEFINE_PER_CPU(struct erofs_pcpu_vma, percpu_vma[EROFS_NR_PERCPU_VMA]);

unsigned int erofs_lock_pcpu_vm_area(unsigned int nr)
{
	read_lock(&percpu_vmalock[nr]);
	preempt_disable();
	pagefault_disable();
	return percpu_vma_maxpages[nr];
}

void erofs_unlock_pcpu_vm_area(unsigned int nr)
{
	pagefault_enable();
	preempt_enable();
	read_unlock(&percpu_vmalock[nr]);
}

void *erofs_map_pcpu_vm_area(unsigned int nr, struct page **pages,
			     unsigned int nrpages)
{
	struct erofs_pcpu_vma *area;
	unsigned long addr;

	/* callers should not pass invalid values in */
	DBG_BUGON(nrpages > percpu_vma_maxpages[nr]);
	area = &get_cpu_var(percpu_vma[nr]);

	addr = (unsigned long)area->vm->addr;

	if (area->nr_pages)
		unmap_kernel_range_local(addr, area->nr_pages * PAGE_SIZE);

	/* map_vm_area cannot be used to map part of the vm area */
	map_kernel_range_noflush(addr, nrpages * PAGE_SIZE,
				 PAGE_KERNEL, pages);
	flush_cache_vmap(addr, addr + nrpages * PAGE_SIZE);
	area->nr_pages = nrpages;

	put_cpu_var(percpu_vma[nr]);
	return (void *)addr;
}

#if (EROFS_PCPUBUF_NR_PAGES > 0)
static DEFINE_PER_CPU(void *, percpu_pagebuf);
static DEFINE_PER_CPU(struct list_head, percpu_pagehead);

void *erofs_get_pcpubuf(unsigned int pagenr)
{
	if (pagenr >= EROFS_PCPUBUF_NR_PAGES)
		return ERR_PTR(-ERANGE);

	return (char *)get_cpu_var(percpu_pagebuf) + pagenr * PAGE_SIZE;
}

int erofs_put_pcpubuf(void *buf, unsigned int pagenr)
{
	if (buf && *this_cpu_ptr(&percpu_pagebuf) + pagenr * PAGE_SIZE != buf)
		return -EINVAL;

	put_cpu_var(percpu_pagebuf);
	return 0;
}

static int erofs_pcpubuf_cpu_prepare(unsigned int cpu)
{
	struct list_head *const list = &per_cpu(percpu_pagehead, cpu);
	struct page *pages[EROFS_PCPUBUF_NR_PAGES];
	void *ptr;
	unsigned int i;

	INIT_LIST_HEAD(list);
	for (i = 0; i < EROFS_PCPUBUF_NR_PAGES; ++i) {
		pages[i] = alloc_pages(GFP_KERNEL, 0);
		if (!pages[i])
			goto fail_nomem;
		list_add_tail(&pages[i]->lru, list);
	}

	ptr = erofs_vmap(pages, EROFS_PCPUBUF_NR_PAGES);
	if (!ptr)
		goto fail_nomem;

	per_cpu(percpu_pagebuf, cpu) = ptr;
	return 0;
fail_nomem:
	while (i)
		erofs_putpage(pages[--i]);
	INIT_LIST_HEAD(list);
	per_cpu(percpu_pagebuf, cpu) = NULL;
	errln("failed to allocate pcpubuf for cpu %u", cpu);
	return -ENOMEM;
}

static void erofs_pcpubuf_cpu_dead(unsigned int cpu)
{
	struct list_head *const list = &per_cpu(percpu_pagehead, cpu);
	void **const pptr = &per_cpu(percpu_pagebuf, cpu);

	erofs_vunmap(*pptr, EROFS_PCPUBUF_NR_PAGES);
	if (list->next != list->prev)
		erofs_put_pages_list(list);
	*pptr = NULL;
}
#else
void *erofs_get_pcpubuf(unsigned int pagenr) { return ERR_PTR(-ENOTSUPP); }
int erofs_put_pcpubuf(void *buf, unsigned int pagenr) { return -ENOTSUPP; }
static int erofs_pcpubuf_cpu_prepare(unsigned int cpu) { return 0; }
static void erofs_pcpubuf_cpu_dead(unsigned int cpu) {}
#endif

static int erofs_cpu_prepare(unsigned int cpu)
{
	unsigned int i;

	for (i = 0; i < EROFS_NR_PERCPU_VMA; ++i) {
		struct erofs_pcpu_vma *area = &per_cpu(percpu_vma[i], cpu);
		struct vm_struct *vm;
		unsigned size;

repeat:
		/*
		 * Make sure we don't leak memory if a cpu UP notification
		 * and erofs_register_cpu_notifier() race and both call
		 * cpu_up() on the same cpu
		 */
		vm = READ_ONCE(area->vm);
		size = percpu_vma_maxpages[i] * PAGE_SIZE;
		if (vm && get_vm_area_size(vm) == size)
			return 0;

		if (!size) {
			if (!vm)
				continue;

			write_lock(&percpu_vmalock[i]);
			if (get_vm_area_size(vm)) {
				write_unlock(&percpu_vmalock[i]);
				goto repeat;
			}
			vm = area->vm;
			area->vm = NULL;
			write_unlock(&percpu_vmalock[i]);
			free_vm_area(area->vm);
			continue;
		}

		vm = alloc_vm_area(size, NULL);
		if (!vm)
			return -ENOMEM;

		write_lock(&percpu_vmalock[i]);
		if (percpu_vma_maxpages[i] * PAGE_SIZE != size) {
			write_unlock(&percpu_vmalock[i]);
			free_vm_area(vm);
			goto repeat;
		}

		if (vm || get_vm_area_size(vm) == size) {
			area->vm = vm;
			area->nr_pages = 0;
			vm = NULL;
		}
		write_unlock(&percpu_vmalock[i]);

		if (vm)
			free_vm_area(vm);
	}
	erofs_pcpubuf_cpu_prepare(cpu);
	return 0;
}

static int erofs_cpu_dead(unsigned int cpu)
{
	unsigned int i;

	for (i = 0; i < EROFS_NR_PERCPU_VMA; ++i) {
		struct erofs_pcpu_vma *area = &per_cpu(percpu_vma[i], cpu);
		struct vm_struct *vm;

		write_lock(&percpu_vmalock[i]);
		if (!area->vm) {
			write_unlock(&percpu_vmalock[i]);
			continue;
		}

		vm = area->vm;
		area->vm = NULL;
		write_unlock(&percpu_vmalock[i]);
		free_vm_area(vm);
	}
	erofs_pcpubuf_cpu_dead(cpu);
	return 0;
}

static enum cpuhp_state hp_online;

int __init erofs_register_cpu_notifier(void)
{
	int err, i;

	for (i = 0; i < EROFS_NR_PERCPU_VMA; ++i)
		rwlock_init(&percpu_vmalock[i]);

	err = cpuhp_setup_state(CPUHP_AP_ONLINE_DYN, "fs/erofs:online",
				erofs_cpu_prepare, erofs_cpu_dead);
	if (err < 0)
		return err;

	hp_online = err;
	return 0;
}

void erofs_unregister_cpu_notifier(void)
{
	cpuhp_remove_state(hp_online);
}

/* global shrink count (for all mounted EROFS instances) */
static atomic_long_t erofs_global_shrink_cnt;

#ifdef CONFIG_EROFS_FS_ZIP
#define __erofs_workgroup_get(grp)	atomic_inc(&(grp)->refcount)
#define __erofs_workgroup_put(grp)	atomic_dec(&(grp)->refcount)

static int erofs_workgroup_get(struct erofs_workgroup *grp)
{
	int o;

repeat:
	o = erofs_wait_on_workgroup_freezed(grp);
	if (unlikely(o <= 0))
		return -1;

	if (unlikely(atomic_cmpxchg(&grp->refcount, o, o + 1) != o))
		goto repeat;

	/* decrease refcount paired by erofs_workgroup_put */
	if (unlikely(o == 1))
		atomic_long_dec(&erofs_global_shrink_cnt);
	return 0;
}

struct erofs_workgroup *erofs_find_workgroup(struct super_block *sb,
					     pgoff_t index, bool *tag)
{
	struct erofs_sb_info *sbi = EROFS_SB(sb);
	struct erofs_workgroup *grp;

repeat:
	rcu_read_lock();
	grp = radix_tree_lookup(&sbi->workstn_tree, index);
	if (grp) {
		*tag = xa_pointer_tag(grp);
		grp = xa_untag_pointer(grp);

		if (erofs_workgroup_get(grp)) {
			/* prefer to relax rcu read side */
			rcu_read_unlock();
			goto repeat;
		}

		DBG_BUGON(index != grp->index);
	}
	rcu_read_unlock();
	return grp;
}

int erofs_register_workgroup(struct super_block *sb,
			     struct erofs_workgroup *grp,
			     bool tag)
{
	struct erofs_sb_info *sbi;
	int err;

	/* grp shouldn't be broken or used before */
	if (unlikely(atomic_read(&grp->refcount) != 1)) {
		DBG_BUGON(1);
		return -EINVAL;
	}

	err = radix_tree_preload(GFP_NOFS);
	if (err)
		return err;

	sbi = EROFS_SB(sb);
	erofs_workstn_lock(sbi);

	grp = xa_tag_pointer(grp, tag);

	/*
	 * Bump up reference count before making this workgroup
	 * visible to other users in order to avoid potential UAF
	 * without serialized by erofs_workstn_lock.
	 */
	__erofs_workgroup_get(grp);

	err = radix_tree_insert(&sbi->workstn_tree,
				grp->index, grp);
	if (unlikely(err))
		/*
		 * it's safe to decrease since the workgroup isn't visible
		 * and refcount >= 2 (cannot be freezed).
		 */
		__erofs_workgroup_put(grp);

	erofs_workstn_unlock(sbi);
	radix_tree_preload_end();
	return err;
}

static void  __erofs_workgroup_free(struct erofs_workgroup *grp)
{
	atomic_long_dec(&erofs_global_shrink_cnt);
	erofs_workgroup_free_rcu(grp);
}

int erofs_workgroup_put(struct erofs_workgroup *grp)
{
	int count = atomic_dec_return(&grp->refcount);

	if (count == 1)
		atomic_long_inc(&erofs_global_shrink_cnt);
	else if (!count)
		__erofs_workgroup_free(grp);
	return count;
}

#ifdef EROFS_FS_HAS_MANAGED_CACHE
/* for cache-managed case, customized reclaim paths exist */
static void erofs_workgroup_unfreeze_final(struct erofs_workgroup *grp)
{
	erofs_workgroup_unfreeze(grp, 0);
	__erofs_workgroup_free(grp);
}

static bool erofs_try_to_release_workgroup(struct erofs_sb_info *sbi,
					   struct erofs_workgroup *grp,
					   bool cleanup)
{
	/*
	 * for managed cache enabled, the refcount of workgroups
	 * themselves could be < 0 (freezed). So there is no guarantee
	 * that all refcount > 0 if managed cache is enabled.
	 */
	if (!erofs_workgroup_try_to_freeze(grp, 1))
		return false;

	/*
	 * note that all cached pages should be unlinked
	 * before delete it from the radix tree.
	 * Otherwise some cached pages of an orphan old workgroup
	 * could be still linked after the new one is available.
	 */
	if (erofs_try_to_free_all_cached_pages(sbi, grp)) {
		erofs_workgroup_unfreeze(grp, 1);
		return false;
	}

	/*
	 * it is impossible to fail after the workgroup is freezed,
	 * however in order to avoid some race conditions, add a
	 * DBG_BUGON to observe this in advance.
	 */
	DBG_BUGON(xa_untag_pointer(radix_tree_delete(&sbi->workstn_tree,
						     grp->index)) != grp);

	/*
	 * if managed cache is enable, the last refcount
	 * should indicate the related workstation.
	 */
	erofs_workgroup_unfreeze_final(grp);
	return true;
}

#else
/* for nocache case, no customized reclaim path at all */
static bool erofs_try_to_release_workgroup(struct erofs_sb_info *sbi,
					   struct erofs_workgroup *grp,
					   bool cleanup)
{
	int cnt = atomic_read(&grp->refcount);

	DBG_BUGON(cnt <= 0);
	DBG_BUGON(cleanup && cnt != 1);

	if (cnt > 1)
		return false;

	DBG_BUGON(xa_untag_pointer(radix_tree_delete(&sbi->workstn_tree,
						     grp->index)) != grp);

	/* (rarely) could be grabbed again when freeing */
	erofs_workgroup_put(grp);
	return true;
}

#endif

unsigned long erofs_shrink_workstation(struct erofs_sb_info *sbi,
				       unsigned long nr_shrink,
				       bool cleanup)
{
	pgoff_t first_index = 0;
	void *batch[PAGEVEC_SIZE];
	unsigned int freed = 0;

	int i, found;
repeat:
	erofs_workstn_lock(sbi);

	found = radix_tree_gang_lookup(&sbi->workstn_tree,
				       batch, first_index, PAGEVEC_SIZE);

	for (i = 0; i < found; ++i) {
		struct erofs_workgroup *grp = xa_untag_pointer(batch[i]);

		first_index = grp->index + 1;

		/* try to shrink each valid workgroup */
		if (!erofs_try_to_release_workgroup(sbi, grp, cleanup))
			continue;

		++freed;
		if (unlikely(!--nr_shrink))
			break;
	}
	erofs_workstn_unlock(sbi);

	if (i && nr_shrink)
		goto repeat;
	return freed;
}

#endif

/* protected by 'erofs_sb_list_lock' */
static unsigned int shrinker_run_no;

/* protects the mounted 'erofs_sb_list' */
static DEFINE_SPINLOCK(erofs_sb_list_lock);
static LIST_HEAD(erofs_sb_list);

void erofs_register_super(struct super_block *sb)
{
	struct erofs_sb_info *sbi = EROFS_SB(sb);

	mutex_init(&sbi->umount_mutex);

	spin_lock(&erofs_sb_list_lock);
	list_add(&sbi->list, &erofs_sb_list);
	spin_unlock(&erofs_sb_list_lock);
}

void erofs_unregister_super(struct super_block *sb)
{
	spin_lock(&erofs_sb_list_lock);
	list_del(&EROFS_SB(sb)->list);
	spin_unlock(&erofs_sb_list_lock);
}

static unsigned long erofs_shrink_count(struct shrinker *shrink,
					struct shrink_control *sc)
{
	return atomic_long_read(&erofs_global_shrink_cnt);
}

static unsigned long erofs_shrink_scan(struct shrinker *shrink,
				       struct shrink_control *sc)
{
	struct erofs_sb_info *sbi;
	struct list_head *p;

	unsigned long nr = sc->nr_to_scan;
	unsigned int run_no;
	unsigned long freed = 0;

	spin_lock(&erofs_sb_list_lock);
	do
		run_no = ++shrinker_run_no;
	while (run_no == 0);

	/* Iterate over all mounted superblocks and try to shrink them */
	p = erofs_sb_list.next;
	while (p != &erofs_sb_list) {
		sbi = list_entry(p, struct erofs_sb_info, list);

		/*
		 * We move the ones we do to the end of the list, so we stop
		 * when we see one we have already done.
		 */
		if (sbi->shrinker_run_no == run_no)
			break;

		if (!mutex_trylock(&sbi->umount_mutex)) {
			p = p->next;
			continue;
		}

		spin_unlock(&erofs_sb_list_lock);
		sbi->shrinker_run_no = run_no;

#ifdef CONFIG_EROFS_FS_ZIP
		freed += erofs_shrink_workstation(sbi, nr, false);
#endif

		spin_lock(&erofs_sb_list_lock);
		/* Get the next list element before we move this one */
		p = p->next;

		/*
		 * Move this one to the end of the list to provide some
		 * fairness.
		 */
		list_move_tail(&sbi->list, &erofs_sb_list);
		mutex_unlock(&sbi->umount_mutex);

		if (freed >= nr)
			break;
	}
	spin_unlock(&erofs_sb_list_lock);
	return freed;
}

struct shrinker erofs_shrinker_info = {
	.scan_objects = erofs_shrink_scan,
	.count_objects = erofs_shrink_count,
	.seeks = DEFAULT_SEEKS,
};

