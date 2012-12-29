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
#include <stdbool.h>

#define NULL ((void *)0)
#define KNODE_DEAD      1LU
#define KNODE_KLIST_MASK    ~KNODE_DEAD

/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */
struct list_head {
    struct list_head *next, *prev;
};

static inline void INIT_LIST_HEAD(struct list_head *list)
{
    list->next = list;
    list->prev = list;
}

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline __attribute__((always_inline)) void __list_add(
        struct list_head *new, struct list_head *prev, struct list_head *next) {
    next->prev = new;
    new->next = next;
    new->prev = prev;
    prev->next = new;
}

/**
 * list_add_tail - add a new entry
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 */
static inline __attribute__((always_inline)) void list_add_tail(
        struct list_head *new, struct list_head *head) {
    __list_add(new, head->prev, head);
}

/*
 * Delete a list entry by making the prev/next entries
 * point to each other.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static inline void __list_del(struct list_head * prev, struct list_head * next)
{
    next->prev = prev;
    prev->next = next;
}

/**
 * list_del - deletes entry from list.
 * @entry: the element to delete from the list.
 * Note: list_empty() on entry does not return true after this, the entry is
 * in an undefined state.
 */
static inline void list_del(struct list_head *entry)
{
    __list_del(entry->prev, entry->next);
    /*
     * These are non-NULL pointers that will result in page faults
     * under normal circumstances, used to verify that nobody uses
     * non-initialized list entries.
     */
    entry->next = ((void *) 0x00100100 + (0x0UL));
    entry->prev = ((void *) 0x00200200 + (0x0UL));
}

/**
 * list_del_init - deletes entry from list and reinitialize it.
 * @entry: the element to delete from the list.
 */
static inline void list_del_init(struct list_head *entry)
{
    __list_del(entry->prev, entry->next);
    INIT_LIST_HEAD(entry);
}

/****************************************************************************/
typedef struct {
    int counter;
} atomic_t;

struct kref {
    atomic_t refcount;
};

struct klist_node {
    void            *n_klist;   /* never access directly */
    struct list_head    n_node;
    struct kref     n_ref;
};

struct kobject {
    const char      *name;
    struct list_head    entry;
//  struct kobject      *parent;
    struct kset     *kset;
//  struct kobj_type    *ktype;
//  struct sysfs_dirent *sd;
    struct kref     kref;
    unsigned int state_initialized:1;
    unsigned int state_in_sysfs:1;
    unsigned int state_add_uevent_sent:1;
    unsigned int state_remove_uevent_sent:1;
//  unsigned int uevent_suppress:1;
};

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
struct kset {
    struct list_head list;
    struct kobject kobj;
//  const struct kset_uevent_ops *uevent_ops;
};

struct klist {
    struct list_head    k_list;
    void            (*get)(struct klist_node *);
    void            (*put)(struct klist_node *);
};

struct klist_iter {
    struct klist        *i_klist;
    struct klist_node   *i_cur;
};

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
void klist_init(struct klist *k, void (*get)(struct klist_node *),
        void (*put)(struct klist_node *))
{
    INIT_LIST_HEAD(&k->k_list);
    k->get = get;
    k->put = put;
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
struct device_type {
    const char *name;
//  const struct attribute_group **groups;
//  int (*uevent)(struct device *dev, struct kobj_uevent_env *env);
//  char *(*devnode)(struct device *dev, mode_t *mode);
//  void (*release)(struct device *dev);
//
//  const struct dev_pm_ops *pm;
};

struct device {
    struct device       *parent;

//  struct device_private   *p;
//
//  struct kobject kobj;
//  const char      *init_name; /* initial name of the device */
    struct device_type  *type;
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
    struct klist_node   knode_class;
//  struct class        *class;
//  const struct attribute_group **groups;  /* optional groups */
//
//  void    (*release)(struct device *dev);
};

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
struct class_private {
    struct kset class_subsys;
    struct klist class_devices;
    struct list_head class_interfaces;
    struct kset class_dirs;
    struct class *class;
};

struct attribute {
    const char      *name;
//  struct module       *owner;
//  mode_t          mode;
//#ifdef CONFIG_DEBUG_LOCK_ALLOC
//  struct lock_class_key   *key;
//  struct lock_class_key   skey;
//#endif
};

struct class_attribute {
    struct attribute attr;
//  ssize_t (*show)(struct class *class, struct class_attribute *attr,
//          char *buf);
//  ssize_t (*store)(struct class *class, struct class_attribute *attr,
//          const char *buf, size_t count);
};

/*
 * device classes
 */
struct class {
    const char      *name;
//  struct module       *owner;
//
    struct class_attribute      *class_attrs;
//  struct device_attribute     *dev_attrs;
    struct kobject          *dev_kobj;
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
    struct class_private *p;
};

struct class_dev_iter {
    struct klist_iter       ki;
    const struct device_type    *type;
};

struct class_interface {
    struct list_head    node;
    struct class        *class;

    int (*add_dev)      (struct device *, struct class_interface *);
    void (*remove_dev)  (struct device *, struct class_interface *);
};

/****************************************************************************/
int nondet;

/**
 * get_device - increment reference count for device.
 * @dev: device.
 *
 * This simply forwards the call to kobject_get(), though
 * we do take care to provide for the case that we get a NULL
 * pointer passed in.
 */
struct device *get_device(struct device *dev)
{
    struct device *a;
    return a;
}

/**
 * put_device - decrement reference count.
 * @dev: device in question.
 */
void put_device(struct device *dev)
{
    return;
}

/**
 *  sysfs_create_file - create an attribute file for an object.
 *  @kobj:  object we're creating for.
 *  @attr:  attribute descriptor.
 */
int sysfs_create_file(struct kobject *x, struct attribute const *y) {
    if ((&nondet > 0))
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
void sysfs_remove_file(struct kobject *x, struct attribute const *y) {
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
int kobject_set_name(struct kobject *kobj, const char *fmt, ...)
{
    return 0;
}

static void klist_release(struct kref *kref)
{
    return;
}

static void kobject_release(struct kref *kref)
{
    return;
}

/****************************************************************************/

#define atomic_set(v,i)             ((v)->counter = (i))
#define atomic_inc(v)               ((v)->counter += 1)
#define atomic_dec_and_test(v)      ((v)->counter-1 == 0)

/**
 * kref_init - initialize object.
 * @kref: object in question.
 */
void kref_init(struct kref *kref)
{
    atomic_set(&kref->refcount, 1);
}

/**
 * kref_get - increment refcount for object.
 * @kref: object.
 */
void kref_get(struct kref *kref)
{
    atomic_inc(&kref->refcount);
}

/**
 * kobject_get - increment refcount for object.
 * @kobj: object.
 */
struct kobject *kobject_get(struct kobject *kobj)
{
    if (kobj)
        kref_get(&kobj->kref);
    return kobj;
}

static inline struct kset *to_kset(struct kobject *kobj)
{
    return kobj ? (struct kset *) kobj : NULL;
}

static inline struct kset *kset_get(struct kset *k)
{
    return k ? to_kset(kobject_get(&k->kobj)) : NULL;
}

/**
 * kref_put - decrement refcount for object.
 * @kref: object.
 * @release: pointer to the function that will clean up the object when the
 *       last reference to the object is released.
 *       This pointer is required, and it is not acceptable to pass kfree
 *       in as this function.
 *
 * Decrement the refcount, and if 0, call release().
 * Return 1 if the object was removed, otherwise return 0.  Beware, if this
 * function returns 0, you still can not count on the kref from remaining in
 * memory.  Only use the return value if you want to see if the kref is now
 * gone, not present.
 */
int kref_put(struct kref *kref, void (*release)(struct kref *kref))
{
    if (atomic_dec_and_test(&kref->refcount)) {
        release(kref);
        return 1;
    }
    return 0;
}

/**
 * kobject_put - decrement refcount for object.
 * @kobj: object.
 *
 * Decrement the refcount, and if 0, call kobject_cleanup().
 */
void kobject_put(struct kobject *kobj)
{
    if (kobj) {
        kref_put(&kobj->kref, kobject_release);
    }
}

static inline void kset_put(struct kset *k)
{
    kobject_put(&k->kobj);
}

static void kobject_init_internal(struct kobject *kobj)
{
    if (!kobj)
        return;
    kref_init(&kobj->kref);
    INIT_LIST_HEAD(&kobj->entry);
    kobj->state_in_sysfs = 0;
    kobj->state_add_uevent_sent = 0;
    kobj->state_remove_uevent_sent = 0;
    kobj->state_initialized = 1;
}

/**
 * kset_init - initialize a kset for use
 * @k: kset
 */
void kset_init(struct kset *k)
{
    kobject_init_internal(&k->kobj);
    INIT_LIST_HEAD(&k->list);
}

/*
 * The actions here must match the index to the string array
 * in lib/kobject_uevent.c
 *
 * Do not add new actions here without checking with the driver-core
 * maintainers. Action strings are not meant to express subsystem
 * or device specific properties. In most cases you want to send a
 * kobject_uevent_env(kobj, KOBJ_CHANGE, env) with additional event
 * specific variables added to the event environment.
 */
enum kobject_action {
    KOBJ_ADD,
    KOBJ_REMOVE,
    KOBJ_CHANGE,
    KOBJ_MOVE,
    KOBJ_ONLINE,
    KOBJ_OFFLINE,
    KOBJ_MAX
};

/**
 * kobject_uevent_env - send an uevent with environmental data
 *
 * @action: action that is happening
 * @kobj: struct kobject that the action is happening to
 * @envp_ext: pointer to environmental data
 *
 * Returns 0 if kobject_uevent() is completed with success or the
 * corresponding error when it fails.
 */
int kobject_uevent_env(struct kobject *kobj, enum kobject_action action,
               char *envp_ext[])
{
    return 0;
}

/**
 * kobject_uevent - notify userspace by ending an uevent
 *
 * @action: action that is happening
 * @kobj: struct kobject that the action is happening to
 *
 * Returns 0 if kobject_uevent() is completed with success or the
 * corresponding error when it fails.
 */
int kobject_uevent(struct kobject *kobj, enum kobject_action action)
{
    return kobject_uevent_env(kobj, action, NULL);
}

static int kobject_add_internal(struct kobject *kobj)
{
    return nondet;
}

/**
 * kset_register - initialize and add a kset.
 * @k: kset.
 */
int kset_register(struct kset *k)
{
    int err;

    if (!k)
        return -22;

    kset_init(k);
    err = kobject_add_internal(&k->kobj);
    if (err)
        return err;
    kobject_uevent(&k->kobj, KOBJ_ADD);
    return 0;
}

/****************************************************************************/

struct kobject *sysfs_dev_char_kobj;
static struct kset *class_kset;
struct class block_class = {
    .name       = "block",
};

int class_create_file(struct class *cls, const struct class_attribute *attr)
{
    int error;
    if (cls)
        error = sysfs_create_file(&cls->p->class_subsys.kobj, &attr->attr);
    else
        error = -22;
    return error;
}

void class_remove_file(struct class *cls, const struct class_attribute *attr) {
    if (cls)
        sysfs_remove_file(&cls->p->class_subsys.kobj, &attr->attr);
}

static struct class *class_get(struct class *cls) {
    if (cls)
        kset_get(&cls->p->class_subsys);
    return cls;
}

static void class_put(struct class *cls) {
    if (cls)
        kset_put(&cls->p->class_subsys);
}

static int add_class_attrs(struct class *cls)
{
    int i;
    int error = 0;

    if (cls->class_attrs) {
        for (i = 0; (cls->class_attrs[i]).attr.name; i++) {
            error = class_create_file(cls, &cls->class_attrs[i]);
            if (error)
                goto error;
        }
    }
done:
    return error;
error:
    while (--i >= 0)
        class_remove_file(cls, &cls->class_attrs[i]);
    goto done;
}

static void klist_class_dev_get(struct klist_node *n)
{
    struct device *dev = (struct device *) n;

    get_device(dev);
}

static void klist_class_dev_put(struct klist_node *n)
{
    struct device *dev = (struct device *) n;

    put_device(dev);
}

int __class_register(struct class *cls, struct lock_class_key *key)
{
    struct class_private *cp;
    int error;

    cp = (struct class_private *) malloc(sizeof(struct class_private));
    if (!cp)
        return -12;
    klist_init(&cp->class_devices, klist_class_dev_get, klist_class_dev_put);
    INIT_LIST_HEAD(&cp->class_interfaces);
    kset_init(&cp->class_dirs);
    error = kobject_set_name(&cp->class_subsys.kobj, "%s", cls->name);
    if (error) {
        free(cp);
        return error;
    }

    /* set the default /sys/dev directory for devices of this class */
    if (!cls->dev_kobj)
        cls->dev_kobj = sysfs_dev_char_kobj;

    /* let the block class directory show up in the root of sysfs */
    if (cls != &block_class)
        cp->class_subsys.kobj.kset = class_kset;
//  cp->class_subsys.kobj.ktype = &class_ktype;
    cp->class = cls;
    cls->p = cp;

    error = kset_register(&cp->class_subsys);
    if (error) {
        free(cp);
        return error;
    }
    error = add_class_attrs(class_get(cls));
    class_put(cls);
    return error;
}

/**
 * klist_iter_init_node - Initialize a klist_iter structure.
 * @k: klist we're iterating.
 * @i: klist_iter we're filling.
 * @n: node to start with.
 *
 * Similar to klist_iter_init(), but starts the action off with @n,
 * instead of with the list head.
 */
void klist_iter_init_node(struct klist *k, struct klist_iter *i,
              struct klist_node *n)
{
    i->i_klist = k;
    i->i_cur = n;
    if (n)
        kref_get(&n->n_ref);
}

/**
 * class_dev_iter_init - initialize class device iterator
 * @iter: class iterator to initialize
 * @class: the class we wanna iterate over
 * @start: the device to start iterating from, if any
 * @type: device_type of the devices to iterate over, NULL for all
 *
 * Initialize class iterator @iter such that it iterates over devices
 * of @class.  If @start is set, the list iteration will start there,
 * otherwise if it is NULL, the iteration starts at the beginning of
 * the list.
 */
void class_dev_iter_init(struct class_dev_iter *iter, struct class *class,
             struct device *start, const struct device_type *type)
{
    struct klist_node *start_knode = NULL;

    if (start)
        start_knode = &start->knode_class;
    klist_iter_init_node(&class->p->class_devices, &iter->ki, start_knode);
    iter->type = type;
}

static int klist_dec_and_del(struct klist_node *n)
{
    return kref_put(&n->n_ref, klist_release);
}

static bool knode_dead(struct klist_node *knode)
{
    return (unsigned long)knode->n_klist & KNODE_DEAD;
}

/**
 * klist_next - Ante up next node in list.
 * @i: Iterator structure.
 *
 * First grab list lock. Decrement the reference count of the previous
 * node, if there was one. Grab the next node, increment its reference
 * count, drop the lock, and return that next node.
 */
struct klist_node *klist_next(struct klist_iter *i)
{
    void (*put)(struct klist_node *) = i->i_klist->put;
    struct klist_node *last = i->i_cur;
    struct klist_node *next;

    if (last) {
        next = (struct klist_node *) (last->n_node.next);
        if (!klist_dec_and_del(last))
            put = NULL;
    } else
        next = (struct klist_node *) (i->i_klist->k_list.next);

    i->i_cur = NULL;
    while (next != (struct klist_node *) (&i->i_klist->k_list)) {
        if (!knode_dead(next)) {
            kref_get(&next->n_ref);
            i->i_cur = next;
            break;
        }
        next = (struct klist_node *) (next->n_node.next);
    }

    if (put && last)
        put(last);
    return i->i_cur;
}

/**
 * class_dev_iter_next - iterate to the next device
 * @iter: class iterator to proceed
 *
 * Proceed @iter to the next device and return it.  Returns NULL if
 * iteration is complete.
 *
 * The returned device is referenced and won't be released till
 * iterator is proceed to the next device or exited.  The caller is
 * free to do whatever it wants to do with the device including
 * calling back into class code.
 */
struct device *class_dev_iter_next(struct class_dev_iter *iter)
{
    struct klist_node *knode;
    struct device *dev;

    while (1) {
        knode = klist_next(&iter->ki);
        if (!knode)
            return NULL;
        dev = (struct device *) knode;
        if (!iter->type || iter->type == dev->type)
            return dev;
    }
}

static struct klist *knode_klist(struct klist_node *knode)
{
    return (struct klist *)
        ((unsigned long)knode->n_klist & KNODE_KLIST_MASK);
}

static void knode_kill(struct klist_node *knode)
{
    /* and no knode should die twice ever either, see we're very humane */
    *(unsigned long *)&knode->n_klist |= KNODE_DEAD;
}

static void klist_put(struct klist_node *n, bool kill)
{
    struct klist *k = knode_klist(n);
    void (*put)(struct klist_node *) = k->put;

    if (kill)
        knode_kill(n);
    if (!klist_dec_and_del(n))
        put = NULL;
    if (put)
        put(n);
}

/**
 * klist_iter_exit - Finish a list iteration.
 * @i: Iterator structure.
 *
 * Must be called when done iterating over list, as it decrements the
 * refcount of the current node. Necessary in case iteration exited before
 * the end of the list was reached, and always good form.
 */
void klist_iter_exit(struct klist_iter *i)
{
    if (i->i_cur) {
        klist_put(i->i_cur, false);
        i->i_cur = NULL;
    }
}

/**
 * class_dev_iter_exit - finish iteration
 * @iter: class iterator to finish
 *
 * Finish an iteration.  Always call this function after iteration is
 * complete whether the iteration ran till the end or not.
 */
void class_dev_iter_exit(struct class_dev_iter *iter)
{
    klist_iter_exit(&iter->ki);
}

/**
 * class_for_each_device - device iterator
 * @class: the class we're iterating
 * @start: the device to start with in the list, if any.
 * @data: data for the callback
 * @fn: function to be called for each device
 *
 * Iterate over @class's list of devices, and call @fn for each,
 * passing it @data.  If @start is set, the list iteration will start
 * there, otherwise if it is NULL, the iteration starts at the
 * beginning of the list.
 *
 * We check the return of @fn each time. If it returns anything
 * other than 0, we break out and return that value.
 *
 * @fn is allowed to do anything including calling back into class
 * code.  There's no locking restriction.
 */
int class_for_each_device(struct class *class, struct device *start,
              void *data, int (*fn)(struct device *, void *))
{
    struct class_dev_iter iter;
    struct device *dev;
    int error = 0;

    if (!class)
        return -22;
    if (!class->p) {
        return -22;
    }

    class_dev_iter_init(&iter, class, start, NULL);
    while ((dev = class_dev_iter_next(&iter))) {
        error = fn(dev, data);
        if (error)
            break;
    }
    class_dev_iter_exit(&iter);

    return error;
}

int class_interface_register(struct class_interface *class_intf)
{
    struct class *parent;
    struct class_dev_iter iter;
    struct device *dev;

    if (!class_intf || !class_intf->class)
        return -19;

    parent = class_get(class_intf->class);
    if (!parent)
        return -22;

    list_add_tail(&class_intf->node, &parent->p->class_interfaces);
    if (class_intf->add_dev) {
        class_dev_iter_init(&iter, parent, NULL, NULL);
        while ((dev = class_dev_iter_next(&iter)))
            class_intf->add_dev(dev, class_intf);
        class_dev_iter_exit(&iter);
    }

    return 0;
}

void class_interface_unregister(struct class_interface *class_intf)
{
    struct class *parent = class_intf->class;
    struct class_dev_iter iter;
    struct device *dev;

    if (!parent)
        return;

    list_del_init(&class_intf->node);
    if (class_intf->remove_dev) {
        class_dev_iter_init(&iter, parent, NULL, NULL);
        while ((dev = class_dev_iter_next(&iter)))
            class_intf->remove_dev(dev, class_intf);
        class_dev_iter_exit(&iter);
    }

    class_put(parent);
}

int main(void)
{
    return 0;
}
