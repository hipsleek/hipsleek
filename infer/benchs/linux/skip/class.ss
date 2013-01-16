/*
 * class.c - basic device class management
 *
 * Copyright (c) 2002-3 Patrick Mochel
 * Copyright (c) 2002-3 Open Source Development Labs
 * Copyright (c) 2003-2004 Greg Kroah-Hartman
 * Copyright (c) 2003-2004 IBM Corp.
 *
 * This file is released under the GPLv2
 *
 */
/* #include <stdbool.h> */

/* #define NULL ((void *)0) */
/* #define KNODE_DEAD      1LU */
/* #define KNODE_KLIST_MASK    ~KNODE_DEAD */

/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */
/* struct list_head { */
/*     struct list_head *next, *prev; */
/* }; */

data list_head {
  list_head next;
  list_head prev;
}

/* dll<q> == self::list_head<q , q> */
/*  or self::list_head<p , q> * p::dll<self> */
/*  inv self!=null; */

dll<n,p,s> == self::list_head<s,p> & n=s
  or self::list_head<n,p> * n::dll<_,self,s> & n!=s 
  inv self!=null;


/* static inline void INIT_LIST_HEAD(struct list_head *list) */
/* { */
/*     list->next = list; */
/*     list->prev = list; */
/* } */

void INIT_LIST_HEAD(list_head list)
  requires list::list_head<_,_>
  ensures list::list_head<list,list>;
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
/* static inline __attribute__((always_inline)) void __list_add( */
/*         struct list_head *new, struct list_head *prev, struct list_head *next) { */
/*     next->prev = new; */
/*     new->next = next; */
/*     new->prev = prev; */
/*     prev->next = new; */
/* } */

void __list_add(list_head new1, list_head prev, list_head next)
  requires new1::list_head<_,_>*prev::list_head<next,pp>*next::list_head<nn,prev>
  ensures prev::list_head<new1,pp> * new1::list_head<next,prev> * next::list_head<nn,new1>;
{
  next.prev = new1;
  new1.next = next;
  new1.prev = prev;
  prev.next = new1;
}
/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
/* static inline __attribute__((always_inline)) void list_add_tail( */
/*         struct list_head *new, struct list_head *head) { */
/*     __list_add(new, head->prev, head); */
/* } */
void list_add_tail(list_head new1, list_head head1)
  requires new1::list_head<_,_> * prev::list_head<head1,pp> * head1::dll<n,prev,s>
  ensures prev::list_head<new1,pp> * new1::list_head<head1,prev> * head1::dll<n,new1,s>;
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
/* static inline void list_del(struct list_head *entry) */
/* { */
/*     __list_del(entry->prev, entry->next); */
/*     /\* */
/*      * These are non-NULL pointers that will result in page faults */
/*      * under normal circumstances, used to verify that nobody uses */
/*      * non-initialized list entries. */
/*      *\/ */
/*     entry->next = ((void *) 0x00100100 + (0x0UL)); */
/*     entry->prev = ((void *) 0x00200200 + (0x0UL)); */
/* } */
void list_del(list_head entry)
  requires p::list_head<_,p> * entry::list_head<n,p> * n::list_head<n,_>
  ensures p::list_head<next,p> * entry::list_head<null,null> * next::list_head<n,p>;
{
    __list_del(entry.prev, entry.next);
    entry.next = null;
    entry.prev = null;
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
/* static inline void list_del_init(struct list_head *entry) */
/* { */
/*     __list_del(entry->prev, entry->next); */
/*     INIT_LIST_HEAD(entry); */
/* } */
void list_del_init(list_head entry)
  requires p::list_head<_,p> * entry::list_head<n,p> * n::list_head<n,_>
  ensures entry::list_head<entry,entry>;
{
    __list_del(entry.prev, entry.next);
    INIT_LIST_HEAD(entry);
}


/****************************************************************************/
data atomic_t {
    int counter;
}

data kref {
    atomic_t refcount;
}

data klist_node {
  //    void            *n_klist;   /* never access directly */
    list_head    n_node;
    kref     n_ref;
}

data char {
  int d;
}

data kobject {
    char      name;
    list_head    entry;
//  struct kobject      *parent;
    kset     kset;
//  struct kobj_type    *ktype;
//  struct sysfs_dirent *sd;
    kref     kref;
    int state_initialized;
    int state_in_sysfs;
    int state_add_uevent_sent;
    int state_remove_uevent_sent;
//  unsigned int uevent_suppress:1;
}

/**
 * struct kset - a set of kobjects of a specific type, belonging to a specific subsystem.
 *
 * A kset defines a group of kobjects.  They can be individually
 * different "types" but overall these kobjects all want to be grouped
 * together and operated on in the same manner.  ksets are used to
 * define the attribute callbacks and other common events that happen to
 * a kobject.
 *
 * @list: the list of all kobjects for this kset
 * @list_lock: a lock for iterating over the kobjects
 * @kobj: the embedded kobject for this kset (recursion, isn't it fun...)
 * @uevent_ops: the set of uevent operations for this kset.  These are
 * called whenever a kobject has something happen to it so that the kset
 * can add new environment variables, or filter out the uevents if so
 * desired.
 */
data kset {
    list_head list;
    kobject kobj;
//  const struct kset_uevent_ops *uevent_ops;
}

data klist {
    list_head    k_list;
//    void            (*get)(struct klist_node *);
//    void            (*put)(struct klist_node *);
}

data klist_iter {
    klist        i_klist;
    klist_node   i_cur;
}

/**
 * klist_init - Initialize a klist structure.
 * @k: The klist we're initializing.
 * @get: The get function for the embedding object (NULL if none)
 * @put: The put function for the embedding object (NULL if none)
 *
 * Initialises the klist structure.  If the klist_node structures are
 * going to be embedded in refcounted objects (necessary for safe
 * deletion) then the get/put arguments are used to initialise
 * functions that take and release references on the embedding
 * objects.
 */
void klist_init(klist k /*, void (*get)(struct klist_node *), */
        /* void (*put)(struct klist_node *) */)
  requires k::klist<list> * list::list_head<_,_>
  ensures  k::klist<list> * list::list_head<list,list>;
{
    INIT_LIST_HEAD(k.k_list);
    /* k->get = get; */
    /* k->put = put; */
}

/****************************************************************************/
/*
 * The type of device, "struct device" is embedded in. A class
 * or bus can contain devices of different types
 * like "partitions" and "disks", "mouse" and "event".
 * This identifies the device type and carries type-specific
 * information, equivalent to the kobj_type of a kobject.
 * If "name" is specified, the uevent will contain it in
 * the DEVTYPE variable.
 */
data device_type {
    char name;
//  const struct attribute_group **groups;
//  int (*uevent)(struct device *dev, struct kobj_uevent_env *env);
//  char *(*devnode)(struct device *dev, mode_t *mode);
//  void (*release)(struct device *dev);
//
//  const struct dev_pm_ops *pm;
}

data device {
    device     parent;

//  struct device_private   *p;
//
//  struct kobject kobj;
//  const char      *init_name; /* initial name of the device */
    device_type  type;
//
//  struct mutex        mutex;  /* mutex to synchronize calls to
//                   * its driver.
//                   */
//
//  struct bus_type *bus;       /* type of bus device is on */
//  struct device_driver *driver;   /* which driver has allocated this
//                     device */
//  void        *platform_data; /* Platform specific data, device
//                     core doesn't touch it */
//  struct dev_pm_info  power;
//
//#ifdef CONFIG_NUMA
//  int     numa_node;  /* NUMA node this device is close to */
//#endif
//  u64     *dma_mask;  /* dma mask (if dma'able device) */
//  u64     coherent_dma_mask;/* Like dma_mask, but for
//                       alloc_coherent mappings as
//                       not all hardware supports
//                       64 bit addresses for consistent
//                       allocations such descriptors. */
//
//  struct device_dma_parameters *dma_parms;
//
//  struct list_head    dma_pools;  /* dma pools (if dma'ble) */
//
//  struct dma_coherent_mem *dma_mem; /* internal for coherent mem
//                       override */
//  /* arch specific additions */
//  struct dev_archdata archdata;
//#ifdef CONFIG_OF
//  struct device_node  *of_node;
//#endif
//
//  dev_t           devt;   /* dev_t, creates the sysfs "dev" */
//
//  spinlock_t      devres_lock;
//  struct list_head    devres_head;
//
    klist_node   knode_class;
//  struct class        *class;
//  const struct attribute_group **groups;  /* optional groups */
//
//  void    (*release)(struct device *dev);
}

/**
 * struct class_private - structure to hold the private to the driver core portions of the class structure.
 *
 * @class_subsys - the struct kset that defines this class.  This is the main kobject
 * @class_devices - list of devices associated with this class
 * @class_interfaces - list of class_interfaces associated with this class
 * @class_dirs - "glue" directory for virtual devices associated with this class
 * @class_mutex - mutex to protect the children, devices, and interfaces lists.
 * @class - pointer back to the struct class that this structure is associated
 * with.
 *
 * This structure is the one that is the actual kobject allowing struct
 * class to be statically allocated safely.  Nothing outside of the driver
 * core should ever touch these fields.
 */
data class_private {
    kset class_subsys;
    klist class_devices;
    list_head class_interfaces;
    kset class_dirs;
    class_ class_;
}

data attribute {
    char      name;
//  struct module       *owner;
//  mode_t          mode;
//#ifdef CONFIG_DEBUG_LOCK_ALLOC
//  struct lock_class_key   *key;
//  struct lock_class_key   skey;
//#endif
}

data class_attribute {
    attribute attr;
//  ssize_t (*show)(struct class *class, struct class_attribute *attr,
//          char *buf);
//  ssize_t (*store)(struct class *class, struct class_attribute *attr,
//          const char *buf, size_t count);
}

/*
 * device classes
 */
data class_ {
    char      name;
//  struct module       *owner;
//
    class_attribute      class_attrs;
//  struct device_attribute     *dev_attrs;
    kobject       dev_kobj;
//
//  int (*dev_uevent)(struct device *dev, struct kobj_uevent_env *env);
//  char *(*devnode)(struct device *dev, mode_t *mode);
//
//  void (*class_release)(struct class *class);
//  void (*dev_release)(struct device *dev);
//
//  int (*suspend)(struct device *dev, pm_message_t state);
//  int (*resume)(struct device *dev);
//
//  const struct kobj_ns_type_operations *ns_type;
//  const void *(*namespace)(struct device *dev);
//
//  const struct dev_pm_ops *pm;
//
    class_private p;
}

data class_dev_iter {
    klist_iter       ki;
    device_type    type;
}

data class_interface {
    list_head    node;
    class_       class_;

    /* int (*add_dev)      (struct device *, struct class_interface *); */
    /* void (*remove_dev)  (struct device *, struct class_interface *); */
}

/****************************************************************************/
global int nondet;

/**
 * get_device - increment reference count for device.
 * @dev: device.
 *
 * This simply forwards the call to kobject_get(), though
 * we do take care to provide for the case that we get a NULL
 * pointer passed in.
 */
device get_device(device dev)
  requires true
  ensures true;
/* { */
/*     device *a; */
/*     return a; */
/* } */

/**
 * put_device - decrement reference count.
 * @dev: device in question.
 */
void put_device(device dev)
  requires true
  ensures true;
{
    return;
}

/**
 *  sysfs_create_file - create an attribute file for an object.
 *  @kobj:  object we're creating for.
 *  @attr:  attribute descriptor.
 */
int sysfs_create_file(kobject x, attribute y)
 case {
  nondet > 0 -> ensures res=0;
  nondet <= 0 -> ensures res=-22;
}
{
    if ((nondet > 0))
        return 0;
    else
        return -22;
}

/**
 *  sysfs_remove_file - remove an object attribute.
 *  @kobj:  object we're acting for.
 *  @attr:  attribute descriptor.
 *
 *  Hash the attribute name and kill the victim.
 */
void sysfs_remove_file(kobject x, attribute y)
  requires true
  ensures true;
 {
    return;
}

/**
 * kobject_set_name - Set the name of a kobject
 * @kobj: struct kobject to set the name of
 * @fmt: format string used to build the name
 *
 * This sets the name of the kobject.  If you have already added the
 * kobject to the system, you must call kobject_rename() in order to
 * change the name of the kobject.
 */
int kobject_set_name(kobject kobj, char fmt)
  requires true
  ensures res=0;
{
    return 0;
}

void klist_release(kref kref)
  requires true
  ensures true;
{
    return;
}

void kobject_release(kref kref)
  requires true
  ensures true;
{
    return;
}

/****************************************************************************/

/* #define atomic_set(v,i)             ((v)->counter = (i)) */
/* #define atomic_inc(v)               ((v)->counter += 1) */
/* #define atomic_dec_and_test(v)      ((v)->counter-1 == 0) */

/**
 * kref_init - initialize object.
 * @kref: object in question.
 */
void kref_init(kref kref)
  requires kref::kref<at> * at::atomic_t<_>
  ensures kref::kref<at> * at::atomic_t<c> & c=1;
{
  kref.refcount.counter = 1;
}

/**
 * kref_get - increment refcount for object.
 * @kref: object.
 */
void kref_get(kref kref)
  requires kref::kref<at> * at::atomic_t<c>
  ensures kref::kref<at> * at::atomic_t<c1> & c1= c+1;
{
  kref.refcount.counter = kref.refcount.counter + 1;
}

kset from_kobject_to_kset(kobject kobj)
  case {
  kobj = null -> ensures res=null;
  kobj != null -> requires kobject::kobject<n,en,ks,kr,s1,s2,s3,s4>
    ensures res::kset<l,ko> * ko::kobject<n,en,ks,kr,s1,s2,s3,s4> & l=en;
}

kset to_kset(kobject kobj)
 case {
  kobj = null -> ensures res=null;
  kobj != null -> requires kobject::kobject<n,en,ks,kr,s1,s2,s3,s4>
    ensures res::kset<l,ko> * ko::kobject<n,en,ks,kr,s1,s2,s3,s4> & l=en;
}
{
  /* return kobj ? (struct kset *) kobj : NULL; */
  if kobj==null return null;
  else return from_kobject_to_kset(kobj);
}
