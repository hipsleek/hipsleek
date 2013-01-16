/*
   md.c : Multiple Devices driver for Linux
      Copyright (C) 1998, 1999, 2000 Ingo Molnar

     completely rewritten, based on the MD driver code from Marc Zyngier

   Changes:

   - RAID-1/RAID-5 extensions by Miguel de Icaza, Gadi Oxman, Ingo Molnar
   - RAID-6 extensions by H. Peter Anvin <hpa@zytor.com>
   - boot support for linear and striped mode by Harald Hoyer <HarryH@Royal.Net>
   - kerneld support by Boris Tobotras <boris@xtalk.msk.su>
   - kmod support by: Cyrus Durgin
   - RAID0 bugfixes: Mark Anthony Lisher <markal@iname.com>
   - Devfs support by Richard Gooch <rgooch@atnf.csiro.au>

   - lots of fixes and improvements to the RAID1/RAID5 and generic
     RAID code (such as request based resynchronization):

     Neil Brown <neilb@cse.unsw.edu.au>.

   - persistent bitmap code
     Copyright (C) 2003-2004, Paul Clements, SteelEye Technology, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   You should have received a copy of the GNU General Public License
   (for example /usr/src/linux/COPYING); if not, write to the Free
   Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
*/

/*#define NULL ((void *)0)*/

/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */
/*struct list_head {*/
/*    struct list_head *next, *prev;*/
/*};*/

data list_head {
  list_head next;
  list_head prev;
}

cll<p,s> == self = s
	or self::list_head<n, p> * n::cll<self,s> & self != s
	inv true;

dll<p> == self::list_head<n,p> * n::cll<self,self>
  inv self!=null;


/*********************************************/

void INIT_LIST_HEAD(list_head list)
  requires list::list_head<_,_>
  ensures list::dll<list>;
{
  list.next = list;
  list.prev = list;
}

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
/*
 static inline __attribute__((always_inline)) void __list_add( 
        struct list_head *new, struct list_head *prev, struct list_head *next) { 
    next->prev = new; 
    new->next = next; 
    new->prev = prev; 
    prev->next = new; 
 }
*/

void __list_add(list_head new1, list_head prev, list_head next)
  requires new1::list_head<_,_> * prev::list_head<next,_> & next=prev
  ensures prev::list_head<new1,new1> * new1::list_head<next,prev> & next=prev;
  requires new1::list_head<_,_> * prev::list_head<next,p> * next::dll<prev>
  ensures prev::list_head<new1,p> * new1::list_head<next,prev> * next::dll<new1>;
{
  next.prev = new1;
  new1.next = next;
  new1.prev = prev;
  prev.next = new1;
}

/**
 * list_add - add a new entry
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 */
void list_add(list_head new1, list_head head1)
{
    __list_add(new1, head1, head1.next);
}

/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
/*
 static inline __attribute__((always_inline)) void list_add_tail( 
        struct list_head *new, struct list_head *head) { 
    __list_add(new, head->prev, head); 
 } 
*/
void list_add_tail(list_head new1, list_head head1)
  requires new1::list_head<_,_> * prev::list_head<head1,head1> & head1=prev
  ensures new1::list_head<head1,prev> * prev::list_head<new1,new1> & head1=prev;
  requires new1::list_head<_,_> * prev::list_head<head1,p> * head1::dll<prev>
  ensures new1::list_head<head1,prev> * prev::list_head<new1,p> * head1::dll<new1>;
{
  __list_add(new1, head1.prev, head1);
}

/*
 * Delete a list entry by making the prev/next entries
 * point to each other.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
/* static inline void __list_del(struct list_head * prev, struct list_head * next) */
/* { */
/*     next->prev = prev; */
/*     prev->next = next; */
/* } */
void __list_del(list_head prev, list_head next)
  requires next::list_head<nn,nn> * nn::list_head<next,next> & next=prev
  ensures next::list_head<next,next> * nn::list_head<_,_>  & next=prev;
  requires prev::list_head<_,p> * next::list_head<n,_>
  ensures prev::list_head<next,p> * next::list_head<n,prev>;
{
  next.prev = prev;
  prev.next = next;
}

/**
 * list_del - deletes entry from list.
 * @entry: the element to delete from the list.
 * Note: list_empty() on entry does not return true after this, the entry is
 * in an undefined state.
 */
void list_del(list_head entry)
  requires prev::list_head<entry,entry> * entry::list_head<next,prev> & next=prev
  ensures prev::list_head<prev,prev> * entry::list_head<null,null> & next=prev;
  requires prev::list_head<entry,p> * entry::list_head<next,prev> * 
           next::list_head<nn,entry> * nn::cll<next,ppp>
  ensures prev::list_head<next,p> * entry::list_head<null,null> * 
          next::list_head<nn,prev> * nn::cll<next,ppp>;
{
  __list_del(entry.prev, entry.next);
  entry.next = null;
  entry.prev = null;
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
void list_del_init(list_head entry)
{
    __list_del(entry.prev, entry.next);
    INIT_LIST_HEAD(entry);
}

/**
 * list_empty - tests whether a list is empty
 * @head: the list to test.
 */
bool list_empty(list_head head1)
{
    return (head1.next == head1);
}

/**
 * list_del_rcu - deletes entry from list without re-initialization
 * @entry: the element to delete from the list.
 *
 * Note: list_empty() on entry does not return true after this,
 * the entry is in an undefined state. It is useful for RCU based
 * lockfree traversal.
 *
 * In particular, it means that we can not poison the forward
 * pointers that may still be used for walking the list.
 *
 * The caller must take whatever precautions are necessary
 * (such as holding appropriate locks) to avoid racing
 * with another list-mutation primitive, such as list_del_rcu()
 * or list_add_rcu(), running on this same list.
 * However, it is perfectly legal to run concurrently with
 * the _rcu list-traversal primitives, such as
 * list_for_each_entry_rcu().
 *
 * Note that the caller is not permitted to immediately free
 * the newly deleted entry.  Instead, either synchronize_rcu()
 * or call_rcu() must be used to defer freeing until an RCU
 * grace period has elapsed.
 */
void list_del_rcu(list_head entry)
{
    __list_del(entry.prev, entry.next);
    entry.prev = null;
}

/****************************************************************************/
/*#define LIST_HEAD(name) struct list_head name = { &(name), &(name) }*/
/*
 * Enables to iterate over all existing md arrays
 * all_mddevs_lock protects this list.
 */
/*static LIST_HEAD(all_mddevs);*/
/*static LIST_HEAD(pers_list);*/
/*static LIST_HEAD(all_detected_devices);*/

/****************************************************************************/
data atomic_t {
  int counter;
}

data kref {
  atomic_t refcount;
}

data hd_struct {
    int start_sect;
    int nr_sects;
    int alignment_offset;
//  unsigned int discard_alignment;
//  struct device __dev;
//  struct kobject *holder_dir;
//  int policy, partno;
//
//  unsigned long stamp;
//  int in_flight[2];
//
//  struct disk_stats dkstats;
//
//  struct rcu_head rcu_head;
}

data gendisk {
//  int major;
//  int first_minor;
//  int minors;
//
//  char disk_name[32];
//  char *(*devnode)(struct gendisk *gd, mode_t *mode);
//
//  struct disk_part_tbl *part_tbl;
    hd_struct part0;
//
//  const struct block_device_operations *fops;
//  struct request_queue *queue;
//  void *private_data;
//
//  int flags;
//  struct device *driverfs_dev;
//  struct kobject *slave_dir;
//
//  struct timer_rand_state *random;
//
//  atomic_t sync_io;
//  struct work_struct async_notify;
//  int node_id;
}

data char {
  int d;
}

data kobject {
    char name;
    list_head entry;
//  struct kobject      *parent;
//  struct kset     *kset;
//  struct kobj_type    *ktype;
//  struct sysfs_dirent *sd;
    kref     kref;
//  unsigned int state_initialized:1;
//  unsigned int state_in_sysfs:1;
//  unsigned int state_add_uevent_sent:1;
//  unsigned int state_remove_uevent_sent:1;
//  unsigned int uevent_suppress:1;
}

data mdk_personality
{
    char name;
    int level;
    list_head list;
//  struct module *owner;
//  int (*make_request)(mddev_s *mddev, struct bio *bio);
//  int (*run)(mddev_s *mddev);
//  int (*stop)(mddev_s *mddev);
//  void (*status)(struct seq_file *seq, mddev_s *mddev);
//  /* error_handler must set ->faulty and clear ->in_sync
//   * if appropriate, and should abort recovery if needed
//   */
//  void (*error_handler)(mddev_s *mddev, mdk_rdev_s *rdev);
//  int (*hot_add_disk) (mddev_s *mddev, mdk_rdev_s *rdev);
//  int (*hot_remove_disk) (mddev_s *mddev, int number);
//  int (*spare_active) (mddev_s *mddev);
//  int (*sync_request)(mddev_s *mddev, int sector_nr, int *skipped, int go_faster);
//  int (*resize) (mddev_s *mddev, int sectors);
//  int (*size) (mddev_s *mddev, int sectors, int raid_disks);
//  int (*check_reshape) (mddev_s *mddev);
//  int (*start_reshape) (mddev_s *mddev);
//  void (*finish_reshape) (mddev_s *mddev);
//  /* quiesce moves between quiescence states
//   * 0 - fully active
//   * 1 - no new requests allowed
//   * others - reserved
//   */
//  void (*quiesce) (mddev_s *mddev, int state);
//  /* takeover is used to transition an array from one
//   * personality to another.  The new personality must be able
//   * to handle the data in the current layout.
//   * e.g. 2drive raid1 -> 2drive raid5
//   *      ndrive raid5 -> degraded n+1drive raid6 with special layout
//   * If the takeover succeeds, a new 'private' structure is returned.
//   * This needs to be installed and then ->run used to activate the
//   * array.
//   */
//  void *(*takeover) (mddev_s *mddev);
}

data mddev_s
{
//  void                *private;
    mdk_personality      pers;
    int               unit;
    int             md_minor;
    list_head        disks;
//  unsigned long           flags;
//#define MD_CHANGE_DEVS    0   /* Some device status has changed */
//#define MD_CHANGE_CLEAN 1 /* transition to or from 'clean' */
//#define MD_CHANGE_PENDING 2   /* superblock update in progress */
//
//  int             suspended;
//  atomic_t            active_io;
    int             ro;
//
    gendisk          gendisk;
//
    kobject          kobj;
    int             hold_active;
//#define   UNTIL_IOCTL 1
//#define   UNTIL_STOP  2
//
//  /* Superblock information */
    int             major_version;
//                  minor_version,
//                  patch_version;
    int             persistent;
    int                 external;   /* metadata is
                             * managed externally */
//  char                metadata_type[17]; /* externally set*/
//  int             chunk_sectors;
    int                ctime;
    int                utime;
//  int             level, layout;
//  char                clevel[16];
    int             raid_disks;
//  int             max_disks;
    int            dev_sectors;    /* used size of
//                           * component devices */
//  int            array_sectors; /* exported array size */
//  int             external_size; /* size managed
//                          * externally */
    int               events;
//  /* If the last 'event' was simply a clean->dirty transition, and
//   * we didn't write it to the spares, then it is safe and simple
//   * to just decrement the event count on a dirty->clean transition.
//   * So we record that possibility here.
//   */
//  int             can_decrease_events;
//
//  char                uuid[16];
//
//  /* If the array is being reshaped, we need to record the
//   * new shape and an indication of where we are up to.
//   * This is written to the superblock.
//   * If reshape_position is MaxSector, then no reshape is happening (yet).
//   */
//  int            reshape_position;
    int             delta_disks;
//  int new_level, new_layout;
//  int             new_chunk_sectors;
//
//  struct mdk_thread_s     *thread;    /* management thread */
//  struct mdk_thread_s     *sync_thread;   /* doing resync or reconstruct */
//  int            curr_resync;    /* last block scheduled */
    /* As resync requests can complete out of order, we cannot easily track
     * how much resync has been completed.  So we occasionally pause until
     * everything completes, then set curr_resync_completed to curr_resync.
     * As such it may be well behind the real resync mark, but it is a value
     * we are certain of.
     */
    int            curr_resync_completed;
//  unsigned long           resync_mark;    /* a recent timestamp */
//  int            resync_mark_cnt;/* blocks written at resync_mark */
//  int            curr_mark_cnt; /* blocks scheduled now */
//
//  int            resync_max_sectors; /* may be set by personality */
//
//  int            resync_mismatches; /* count of sectors where
//                              * parity/replica mismatch found
//                              */
//
//  /* allow user-space to request suspension of IO to regions of the array */
//  int            suspend_lo;
//  int            suspend_hi;
//  /* if zero, use the system-wide default */
//  int             sync_speed_min;
//  int             sync_speed_max;
//
//  /* resync even though the same disks are shared among md-devices */
//  int             parallel_resync;
//
//  int             ok_start_degraded;
//  /* recovery/resync flags
//   * NEEDED:   we might need to start a resync/recover
//   * RUNNING:  a thread is running, or about to be started
//   * SYNC:     actually doing a resync, not a recovery
//   * RECOVER:  doing recovery, or need to try it.
//   * INTR:     resync needs to be aborted for some reason
//   * DONE:     thread is done and is waiting to be reaped
//   * REQUEST:  user-space has requested a sync (used with SYNC)
//   * CHECK:    user-space request for check-only, no repair
//   * RESHAPE:  A reshape is happening
//   *
//   * If neither SYNC or RESHAPE are set, then it is a recovery.
//   */
//#define   MD_RECOVERY_RUNNING 0
//#define   MD_RECOVERY_SYNC    1
//#define   MD_RECOVERY_RECOVER 2
//#define   MD_RECOVERY_INTR    3
//#define   MD_RECOVERY_DONE    4
//#define   MD_RECOVERY_NEEDED  5
//#define   MD_RECOVERY_REQUESTED   6
//#define   MD_RECOVERY_CHECK   7
//#define MD_RECOVERY_RESHAPE   8
//#define   MD_RECOVERY_FROZEN  9
//
//  unsigned long           recovery;
    int             recovery_disabled; /* if we detect that recovery
                                * will always fail, set this
                                * so we don't loop trying */

//  int             in_sync;    /* know to not need resync */
//  /* 'open_mutex' avoids races between 'md_open' and 'do_md_stop', so
//   * that we are never stopping an array while it is open.
//   * 'reconfig_mutex' protects all other reconfiguration.
//   * These locks are separate due to conflicting interactions
//   * with bdev->bd_mutex.
//   * Lock ordering is:
//   *  reconfig_mutex -> bd_mutex : e.g. do_md_run -> revalidate_disk
//   *  bd_mutex -> open_mutex:  e.g. __blkdev_get -> md_open
//   */
//  struct mutex            open_mutex;
//  struct mutex            reconfig_mutex;
    atomic_t            active;     /* general refcount */
    atomic_t            openers;    /* number of active opens */

    int             degraded;   /* whether md should consider
                             * adding a spare
                             */
//  int             barriers_work;  /* initialised to true, cleared as soon
//                           * as a barrier request to slave
//                           * fails.  Only supported
//                           */
//  struct bio          *biolist;   /* bios that need to be retried
//                           * because BIO_RW_BARRIER is not supported
//                           */
//
//  atomic_t            recovery_active; /* blocks scheduled, but not written */
//  wait_queue_head_t       recovery_wait;
//  int            recovery_cp;
//  int            resync_min; /* user requested sync
//                           * starts here */
//  int            resync_max; /* resync should pause
//                           * when it gets here */
//
    sysfs_dirent     sysfs_state;   /* handle for 'array_state'
                             * file in sysfs.
                             */
//  struct sysfs_dirent     *sysfs_action;  /* handle for 'sync_action' */
//
//  struct work_struct del_work;    /* used for delayed sysfs removal */
//
//  spinlock_t          write_lock;
//  wait_queue_head_t       sb_wait;    /* for waiting on superblock updates */
//  atomic_t            pending_writes; /* number of active superblock writes */
//
//  unsigned int            safemode;   /* if set, update "clean" superblock
//                           * when no writes pending.
//                           */
//  unsigned int            safemode_delay;
//  struct timer_list       safemode_timer;
//  atomic_t            writes_pending;
//  struct request_queue        *queue; /* for plugging ... */
//
//  struct bitmap                   *bitmap; /* the bitmap for the device */
//  struct {
//      struct file     *file; /* the bitmap file */
//      loff_t          offset; /* offset from superblock of
//                       * start of bitmap. May be
//                       * negative, but not '0'
//                       * For external metadata, offset
//                       * from start of device.
//                       */
//      loff_t          default_offset; /* this is the offset to use when
//                           * hot-adding a bitmap.  It should
//                           * eventually be settable by sysfs.
//                           */
//      struct mutex        mutex;
//      unsigned long       chunksize;
//      unsigned long       daemon_sleep; /* how many seconds between updates? */
//      unsigned long       max_write_behind; /* write-behind mode */
//      int         external;
//  } bitmap_info;
//
//  atomic_t            max_corr_read_errors; /* max read retries */
    list_head        all_mddevs;
//
//  struct attribute_group      *to_remove;
//  /* Generic barrier handling.
//   * If there is a pending barrier request, all other
//   * writes are blocked while the devices are flushed.
//   * The last to finish a flush schedules a worker to
//   * submit the barrier request (without the barrier flag),
//   * then submit more flush requests.
//   */
//  struct bio *barrier;
//  atomic_t flush_pending;
//  struct work_struct barrier_work;
}

data inode {
//  struct hlist_node i_hash;
//  struct list_head i_list;
//  struct list_head i_sb_list;
//  struct list_head i_dentry;
//  unsigned long i_ino;
//  atomic_t i_count;
//  unsigned int i_nlink;
//  uid_t i_uid;
//  gid_t i_gid;
//  int i_rdev;
//  unsigned int i_blkbits;
//  u64 i_version;
    int i_size;

//  struct timespec i_atime;
//  struct timespec i_mtime;
//  struct timespec i_ctime;
//  blkcnt_t i_blocks;
//  unsigned short i_bytes;
//  umode_t i_mode;
//  spinlock_t i_lock;
//  struct mutex i_mutex;
//  struct rw_semaphore i_alloc_sem;
//  const struct inode_operations *i_op;
//  const struct file_operations *i_fop;
//  struct super_block *i_sb;
//  struct file_lock *i_flock;
//  struct address_space *i_mapping;
//  struct address_space i_data;
//
//  struct list_head i_devices;
//  union {
//      struct pipe_inode_info *i_pipe;
//      struct block_device *i_bdev;
//      struct cdev *i_cdev;
//  };
//
//  __u32 i_generation;
//  //# 779 "include/linux/fs.h"
//  unsigned long i_state;
//  unsigned long dirtied_when;
//
//  unsigned int i_flags;
//
//  atomic_t i_writecount;
//
//  struct posix_acl *i_acl;
//  struct posix_acl *i_default_acl;
//
//  void *i_private;
}

//# 806 "include/linux/fs.h"
/*enum inode_i_mutex_lock_class {*/
/*    I_MUTEX_NORMAL,*/
/*    I_MUTEX_PARENT,*/
/*    I_MUTEX_CHILD,*/
/*    I_MUTEX_XATTR,*/
/*    I_MUTEX_QUOTA*/
/*};*/

data block_device {
    int bd_dev;
    inode bd_inode;
//  struct super_block * bd_super;
//  int bd_openers;
//  struct mutex bd_mutex;
//  struct list_head bd_inodes;
//  void * bd_claiming;
//  void * bd_holder;
//  int bd_holders;
//
//  struct list_head bd_holder_list;
//
//  struct block_device * bd_contains;
//  unsigned bd_block_size;
//  struct hd_struct * bd_part;
//
//  unsigned bd_part_count;
//  int bd_invalidated;
//  struct gendisk * bd_disk;
//  struct list_head bd_list;
//
//  unsigned long bd_private;
//
//  int bd_fsfreeze_count;
//
//  struct mutex bd_fsfreeze_mutex;
}

/*
 * Each physical page in the system has a struct page associated with
 * it to keep track of whatever it is we are using the page for at the
 * moment. Note that we have no way to track which tasks are using
 * a page, though if it is a pagecache page, rmap structures can tell us
 * who is mapping it.
 */
data page {
    int flags;        /* Atomic flags, some possibly
                     * updated asynchronously */
    atomic_t _count;        /* Usage count, see below. */
//  union {
//      atomic_t _mapcount; /* Count of ptes mapped in mms,
//                   * to show when page is mapped
//                   * & limit reverse map searches.
//                   */
//      struct {        /* SLUB */
//          u16 inuse;
//          u16 objects;
//      };
//  };
//  union {
//      struct {
//      unsigned long private;      /* Mapping-private opaque data:
//                       * usually used for buffer_heads
//                       * if PagePrivate set; used for
//                       * swp_entry_t if PageSwapCache;
//                       * indicates order in the buddy
//                       * system if PG_buddy is set.
//                       */
//      struct address_space *mapping;  /* If low bit clear, points to
//                       * inode address_space, or NULL.
//                       * If page mapped as anonymous
//                       * memory, low bit is set, and
//                       * it points to anon_vma object:
//                       * see PAGE_MAPPING_ANON below.
//                       */
//      };
//#if USE_SPLIT_PTLOCKS
//      spinlock_t ptl;
//#endif
//      struct kmem_cache *slab;    /* SLUB: Pointer to slab */
//      struct page *first_page;    /* Compound tail pages */
//  };
//  union {
//      pgoff_t index;      /* Our offset within mapping. */
//      void *freelist;     /* SLUB: freelist req. slab lock */
//  };
//  struct list_head lru;       /* Pageout list, eg. active_list
//                   * protected by zone->lru_lock !
//                   */
//  /*
//   * On machines where all RAM is mapped into kernel address space,
//   * we can simply calculate the virtual address. On machines with
//   * highmem some memory is mapped into kernel virtual memory
//   * dynamically, so we need a place to store that address.
//   * Note that this field could be 16 bits on x86 ... ;)
//   *
//   * Architectures with slow multiplication can define
//   * WANT_PAGE_VIRTUAL in asm/page.h
//   */
//#if defined(WANT_PAGE_VIRTUAL)
//  void *virtual;          /* Kernel virtual address (NULL if
//                     not kmapped, ie. highmem) */
//#endif /* WANT_PAGE_VIRTUAL */
//#ifdef CONFIG_WANT_PAGE_DEBUG_FLAGS
//  unsigned long debug_flags;  /* Use atomic bitops on this */
//#endif
//
//#ifdef CONFIG_KMEMCHECK
//  /*
//   * kmemcheck wants to track the status of each byte in a page; this
//   * is a pointer to such a status block. NULL if not tracked.
//   */
//  void *shadow;
//#endif
}

data sysfs_dirent {
    atomic_t        s_count;
    atomic_t        s_active;
//#ifdef CONFIG_DEBUG_LOCK_ALLOC
//  struct lockdep_map  dep_map;
//#endif
//  struct sysfs_dirent *s_parent;
//  struct sysfs_dirent *s_sibling;
//  const char      *s_name;
//
//  const void      *s_ns; /* namespace tag */
//  union {
//      struct sysfs_elem_dir       s_dir;
//      struct sysfs_elem_symlink   s_symlink;
//      struct sysfs_elem_attr      s_attr;
//      struct sysfs_elem_bin_attr  s_bin_attr;
//  };
//
//  unsigned int        s_flags;
//  unsigned short      s_mode;
//  ino_t           s_ino;
//  struct sysfs_inode_attrs *s_iattr;
}

/*
 * MD's 'extended' device
 */
data mdk_rdev_s
{
    list_head same_set;  /* RAID devices within the same set */

    int sectors;       /* Device size (in 512bytes sectors) */
    mddev_s mddev;         /* RAID array if running */
//  int last_events;        /* IO event timestamp */
//
    block_device bdev;  /* block device handle */

    page sb_page;
    int     sb_loaded;
    int       sb_events;
    int    data_offset;    /* start of data in array */
    int    sb_start;   /* offset of the super block (in 512byte sectors) */
//  int     sb_size;    /* bytes in the superblock */
//  int     preferred_minor;    /* autorun support */
//
    kobject  kobj;

    /* A device can be in one of three states based on two flags:
     * Not working:   faulty==1 in_sync==0
     * Fully working: faulty==0 in_sync==1
     * Working, but not
     * in sync with array
     *                faulty==0 in_sync==0
     *
     * It can never have faulty==1, in_sync==1
     * This reduces the burden of testing multiple flags in many cases
     */

    int   flags;
//#define   Faulty      1       /* device is known to have a fault */
//#define   In_sync     2       /* device is in_sync with rest of array */
//#define   WriteMostly 4       /* Avoid reading if at all possible */
//#define   BarriersNotsupp 5       /* BIO_RW_BARRIER is not supported */
//#define   AllReserved 6       /* If whole device is reserved for
//                   * one array */
//#define   AutoDetected    7       /* added by auto-detect */
//#define Blocked       8       /* An error occured on an externally
//                   * managed array, don't allow writes
//                   * until it is cleared */
//  wait_queue_head_t blocked_wait;
//
    int desc_nr;            /* descriptor index in the superblock */
    int raid_disk;          /* role of device in array */
//  int new_raid_disk;      /* role that the device will have in
//                   * the array after a level-change completes.
//                   */
    int saved_raid_disk;        /* role that device used to have in the
//                   * array and could again if we did a partial
//                   * resync from the bitmap
//                   */
    int    recovery_offset;/* If this device has been partially
                     * recovered, this is where we were
                     * up to.
                     */

    atomic_t    nr_pending; /* number of pending requests.
                     * only maintained for arrays that
                     * support hot removal
                     */
    atomic_t    read_errors;    /* number of consecutive read errors that
                     * we have tried to ignore.
                     */
//  struct timespec last_read_error;    /* monotonic time since our
//                       * last read error
//                       */
    atomic_t    corrected_errors; /* number of corrected read errors,
                       * for reporting to userspace and storing
                       * in superblock.
                       */
//  struct work_struct del_work;    /* used for delayed sysfs removal */
//
    sysfs_dirent sysfs_state; /* handle for 'state'
                       * sysfs entry */
}

data seq_file {
    char buf;
    int size;
    int from;
    int count;
    int index;
    int read_pos;
    int version;
//  const struct seq_operations *op;
/*    void *private;*/
}

data super_type  {
    char            name;
//  struct module       *owner;
/*    int         (*load_super)(mdk_rdev_s *rdev, mdk_rdev_s *refdev,*/
/*                      int minor_version);*/
//  int         (*validate_super)(mddev_s *mddev, mdk_rdev_s *rdev);
/*    void            (*sync_super)(mddev_s *mddev, mdk_rdev_s *rdev);*/
/*    int  (*rdev_size_change)(mdk_rdev_s *rdev,*/
/*                        int num_sectors);*/
}

data detected_devices_node {
    list_head list;
    int dev;
}

/****************************************************************************/

void prefetch()
  requires true
  ensures true;
{
    return;
}

/**
 * strcmp - Compare two strings
 * @cs: One string
 * @ct: Another string
 *
 * returns   0 if @cs and @ct are equal,
 *         < 0 if @cs is less than @ct
 *         > 0 if @cs is greater than @ct
 */
int strcmp(char cs, char ct)
{
     int a; return a;
}

void bd_release_from_disk(block_device x, gendisk y){
    return;
}

/**
 *  sysfs_remove_link - remove symlink in object's directory.
 *  @kobj:  object we're acting for.
 *  @name:  name of the symlink to remove.
 */
void sysfs_remove_link(kobject kobj, char name){
    return;
}

void sysfs_put(sysfs_dirent sd){
    return;
}

/**
 * strict_strtoull - convert a string to an unsigned long long strictly
 * @cp: The string to be converted
 * @base: The number base to use
 * @res: The converted result value
 *
 * strict_strtoull converts a string to an unsigned long long only if the
 * string is really an unsigned long long string, any string containing
 * any invalid char at the tail will be rejected and -EINVAL is returned,
 * only a newline char at the tail is acceptible because people generally
 * change a module parameter in the following way:
 *
 *  echo 1024 > /sys/module/e1000/parameters/copybreak
 *
 * echo will append a newline to the tail of the string.
 *
 * It returns 0 if conversion is successful and *res is set to the converted
 * value, otherwise it returns -EINVAL and *res is set to 0.
 *
 * simple_strtoull just ignores the successive invalid characters and
 * return the converted value of prefix part of the string.
 */
int strict_strtoull(char x, int y, int z){
    return 0;
}

/**
 * kobject_init - initialize a kobject structure
 * @kobj: pointer to the kobject to initialize
 * @ktype: pointer to the ktype for this kobject.
 *
 * This function will properly initialize a kobject such that it can then
 * be passed to the kobject_add() call.
 *
 * After this function is called, the kobject MUST be cleaned up by a call
 * to kobject_put(), not by a call to kfree directly to ensure that all of
 * the memory is cleaned up properly.
 */
//void kobject_init(struct kobject *kobj, struct kobj_type *ktype)
//{
//  return;
//}

/*static inline __attribute__((always_inline)) void * ERR_PTR(long error) {*/
/*    return (void *) error;*/
/*}*/

int alloc_disk_sb(mdk_rdev_s rdev)
{
    return 0;
}

/*
 * prevent the device from being mounted, repartitioned or
 * otherwise reused by a RAID array (or any other kernel
 * subsystem), by bd_claiming the device.
 */
int lock_rdev(mdk_rdev_s rdev, int dev, int shared)
{
    int err = 0;
    return err;
}

void unlock_rdev(mdk_rdev_s rdev)
{
    return;
}

void put_page(page page)
{
    return;
}

void free_disk_sb(mdk_rdev_s rdev)
{
    if (rdev.sb_page!=null) {
        put_page(rdev.sb_page);
        rdev.sb_loaded = 0;
        rdev.sb_page = null;
        rdev.sb_start = 0;
        rdev.sectors = 0;
    }
}

void set_disk_ro(gendisk disk, int flag)
{
    return;
}

void md_stop(mddev_s mddev)
{
    return;
}

void sysfs_notify_dirent(sysfs_dirent sd)
{
    return;
}

void set_capacity(gendisk disk, int size) {
    disk.part0.nr_sects = size;
}

/**
 * blk_integrity_unregister - Remove block integrity profile
 * @disk:   disk whose integrity profile to deallocate
 *
 * Description: This function frees all memory used by the block
 * integrity profile.  To be called at device teardown.
 */
void blk_integrity_unregister(gendisk disk)
{
    return;
}

/**
 * revalidate_disk - wrapper for lower-level driver's revalidate_disk call-back
 * @disk: struct gendisk to be revalidated
 *
 * This routine is a wrapper for lower-level driver's revalidate_disk
 * call-backs.  It is used to do common pre and post operations needed
 * for all revalidate_disk operations.
 */
int revalidate_disk(gendisk disk)
{
    int ret = 0;
    return ret;
}

/*int register_md_personality(mdk_personality p)*/
/*{*/
/*    list_add_tail(p.list, &pers_list);*/
/*    return 0;*/
/*}*/

int unregister_md_personality(mdk_personality p)
{
    list_del_init(p.list);
    return 0;
}

/*
 * lets try to run arrays based on all disks that have arrived
 * until now. (those are in pending_raid_disks)
 *
 * the method: pick the first pending disk, collect all disks with
 * the same UUID, remove all from the pending list and put them into
 * the 'same_array' list. Then order this list based on superblock
 * update time (freshest comes first), kick out 'old' disks and
 * compare superblocks. If everything's fine then run it.
 *
 * If "unit" is allocated, then bump its reference count
 */
void autorun_devices(int part)
{
    return;
}

/*static inline __attribute__((always_inline)) long IS_ERR(const void *ptr)*/
/*{*/
/*    return __builtin_expect(!!(((unsigned long)ptr) >= (unsigned long)-4095), 0);*/
/*}*/

/*static inline void set_bit(int nr, void *addr)*/
/*{*/
/*    return;*/
/*}*/

/****************************************************************************/
void atomic_set(atomic_t v, int i){
  v.counter = i;
}

void atomic_inc(atomic_t v){
  v.counter = v.counter + 1;
}

bool atomic_dec_and_test(atomic_t v){
  v.counter = v.counter - 1;
  return (v.counter==0);
}

int atomic_read(atomic_t v){
  return v.counter;
}

/**
 * kref_init - initialize object.
 * @kref: object in question.
 */
void kref_init(kref kref)
{
    atomic_set(kref.refcount, 1);
}

/**
 * kref_get - increment refcount for object.
 * @kref: object.
 */
void kref_get(kref kref)
{
    atomic_inc(kref.refcount);
}

/**
 * kobject_get - increment refcount for object.
 * @kobj: object.
 */
kobject kobject_get(kobject kobj)
{
    if (kobj!=null)
        kref_get(kobj.kref);
    return kobj;
}

int overlaps(int s1, int l1, int s2, int l2)
{
    /* check if two start/length pairs overlap */
    if (s1+l1 <= s2)
        return 0;
    if (s2+l2 <= s1)
        return 0;
    return 1;
}

/****************************************************************************/

