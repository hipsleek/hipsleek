/*
 * drivers/pci/pci-driver.c
 *
 * (C) Copyright 2002-2004, 2007 Greg Kroah-Hartman <greg@kroah.com>
 * (C) Copyright 2007 Novell Inc.
 *
 * Released under the GPL v2 only.
 *
 */

//#define NULL ((void *)0)

/*
 * Simple doubly linked list implementation.
 *
 * Some of the internal functions ("__xxx") are useful when
 * manipulating whole lists rather than single entries, as
 * sometimes we already know the next/prev entries and we can
 * generate better code by using them directly rather than
 * using the generic single-entry routines.
 */
/*
 struct list_head { 
    struct list_head *next, *prev; 
 };
*/ 
data list_head {
  list_head next;
  list_head prev;
}

cll<p,s> == self = s
	or self::list_head<n, p> * n::cll<self,s> & self != s
	inv true;

cllN<p,s,size> == self = s & size=0
	or self::list_head<n, p> * n::cllN<self,s,size-1> & self != s
	inv size>=0;

dll<p> == self::list_head<n,p> * n::cll<self,self>
  inv self!=null;

dllN<p,size> == self::list_head<n,p> * n::cllN<self,self,size-1>
  inv self!=null & size>=1;

/*********************************************/

relation H(int a).
void INIT_LIST_HEAD(list_head list)
  infer [H]
  requires list::list_head<_,_>
  ensures list::dllN<list,size> & H(size);
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

relation P(int a).
relation Q1(int a, int b).
/*relation Q(int a).*/
void __list_add_1(list_head new1, list_head prev, list_head next)
  requires new1::list_head<_,_> * prev::list_head<next,_> & next=prev
  ensures prev::list_head<new1,new1> * new1::list_head<next,prev> & next=prev;
  infer [P,Q1]
  requires new1::list_head<_,_> * prev::list_head<next,p> * next::dllN<prev,size> & P(size)
  ensures prev::list_head<new1,p> * new1::list_head<next,prev> * next::dllN<new1,size1> & Q1(size1,size);
{
  next.prev = new1;
  new1.next = next;
  new1.prev = prev;
  prev.next = new1;
}

void __list_add(list_head new1, list_head prev, list_head next)
  requires new1::list_head<_,_> * prev::list_head<next,_> & next=prev
  ensures prev::list_head<new1,new1> * new1::list_head<next,prev> & next=prev;
  requires new1::list_head<_,_> * prev::list_head<next,p> * next::dllN<prev,size>
  ensures prev::list_head<new1,p> * new1::list_head<next,prev> * next::dllN<new1,size>;

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
void list_add_tail_1(list_head new1, list_head head1)
  requires new1::list_head<_,_> * prev::list_head<head1,head1> & head1=prev
  ensures new1::list_head<head1,prev> * prev::list_head<new1,new1> & head1=prev;
  infer [P,Q1]
  requires new1::list_head<_,_> * prev::list_head<head1,p> * head1::dllN<prev,size> & P(size)
  ensures new1::list_head<head1,prev> * prev::list_head<new1,p> * head1::dllN<new1,size1> & Q1(size1,size);
{
  __list_add(new1, head1.prev, head1);
}

void list_add_tail(list_head new1, list_head head1)
  requires new1::list_head<_,_> * prev::list_head<head1,head1> & head1=prev
  ensures new1::list_head<head1,prev> * prev::list_head<new1,new1> & head1=prev;
  requires new1::list_head<_,_> * prev::list_head<head1,p> * head1::dllN<prev,size>
  ensures new1::list_head<head1,prev> * prev::list_head<new1,p> * head1::dllN<new1,size>;

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
           next::list_head<nn,entry> * nn::cllN<next,ppp,size>
  ensures prev::list_head<next,p> * entry::list_head<null,null> * 
          next::list_head<nn,prev> * nn::cllN<next,ppp,size>;

void list_del_1(list_head entry)
  requires prev::list_head<entry,entry> * entry::list_head<next,prev> & next=prev
  ensures prev::list_head<prev,prev> * entry::list_head<null,null> & next=prev;
  infer [P,Q1]
  requires prev::list_head<entry,p> * entry::list_head<next,prev> * 
           next::list_head<nn,entry> * nn::cllN<next,ppp,size> & P(size)
  ensures prev::list_head<next,p> * entry::list_head<null,null> * 
          next::list_head<nn,prev> * nn::cllN<next,ppp,size1> & Q1(size1,size);
{
  __list_del(entry.prev, entry.next);
  entry.next = null;
  entry.prev = null;
}

/****************************************************************************/

/* struct pci_device_id { */
/*  unsigned int vendor, device; /\* Vendor and device ID or PCI_ANY_ID*\/ */
/*  unsigned int subvendor, subdevice; /\* Subsystem ID's or PCI_ANY_ID *\/ */
/*  unsigned int class, class_mask; /\* (class,subclass,prog-if) triplet *\/ */
/*  unsigned long driver_data; /\* Data private to the driver *\/ */
/* }; */

data pci_device_id {
  int vendor; int device; /* Vendor and device ID or PCI_ANY_ID*/
  int subvendor;int subdevice; /* Subsystem ID's or PCI_ANY_ID */
  int class_; int class_mask; /* (class,subclass,prog-if) triplet */
  int driver_data; /* Data private to the driver */
  pci_device_id next;
}

/* struct pci_dynid { */
/*  struct list_head node; */
/*  struct pci_device_id id; */
/* }; */

data pci_dynid {
    list_head node;
    pci_device_id id;
}

/* struct pci_dynids { */
/*  struct list_head list; */
/* }; */

data pci_dynids {
  list_head list;
}

/* struct bus_type { */
/*  const char *name; */
/*  //  int (*probe)(struct device *dev); */
/*  //  int (*remove)(struct device *dev); */
/* }; */

data char {
  int d;
}

data bus_type {
    char name;
    //  int (*probe)(struct device *dev);
    //  int (*remove)(struct device *dev);
}

data module {
    module next;
    char name;
//  int gpl_compatible;
//  struct symbol *unres;
//  int seen;
//  int skip;
//  int has_init;
//  int has_cleanup;
//  struct buffer dev_table_buf;
//  char         srcversion[25];
}

/* struct device_driver { */
/*  const char *name; */
/*  struct bus_type *bus; */
/*  //  int (*probe)(struct device *dev); */
/*  //  int (*remove)(struct device *dev); */
/* }; */

data device_driver {
    char name;
    bus_type bus;
    module owner;
    char mod_name;

//  bool suppress_bind_attrs;
//  int (*probe) (struct device *dev);
//  int (*remove) (struct device *dev);
//  void (*shutdown) (struct device *dev);
//  int (*suspend) (struct device *dev, pm_message_t state);
//  int (*resume) (struct device *dev);
//  const struct attribute_group **groups;
//  const struct dev_pm_ops *pm;
//  struct driver_private *p;
}

/* struct pci_driver { */
/*  struct list_head node; */
/*  char *name; */
/*  const struct pci_device_id *id_table; */
/*  //  int (*probe)(struct pci_dev *dev, const struct pci_device_id *id); */
/*  //  void (*remove)(struct pci_dev *dev); */
/*  struct device_driver driver; */
/*  struct pci_dynids dynids; */
/* }; */

data pci_driver {
    list_head node;
    char name;
    pci_device_id id_table;
    //  int (*probe)(struct pci_dev *dev, const struct pci_device_id *id);
    //  void (*remove)(struct pci_dev *dev);
    device_driver driver;
    pci_dynids dynids;
}

data device {
    device   parent;

//  struct device_private   *p;
//
//  struct kobject kobj;
//  const char      *init_name; /* initial name of the device */
//  struct device_type  *type;
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
//  struct klist_node   knode_class;
//  struct class        *class;
//  const struct attribute_group **groups;  /* optional groups */
//
//  void    (*release)(struct device *dev);
}

data pci_dev {
//  struct list_head bus_list;
//  struct pci_bus *bus;
//  struct pci_bus *subordinate;
//  void *sysdata;
//  struct proc_dir_entry *procent;
//  struct pci_slot *slot;
//  unsigned int devfn;
    int vendor;
    int device;
    int subsystem_vendor;
    int subsystem_device;
    int class_;
//  u8 revision;
//  u8 hdr_type;
//  u8 pcie_cap;
//  u8 pcie_type;
//  u8 rom_base_reg;
//  u8 pin;
//  struct pci_driver *driver;
//  u64 dma_mask;
//  struct device_dma_parameters dma_parms;
//  pci_power_t current_state;
//  int pm_cap;
//  unsigned int pme_support:5;
//  unsigned int pme_interrupt:1;
//  unsigned int d1_support:1;
//  unsigned int d2_support:1;
//  unsigned int no_d1d2:1;
//  unsigned int wakeup_prepared:1;
//  unsigned int d3_delay;
//  pci_channel_state_t error_state;
    device dev;
//  int cfg_size;
//  unsigned int irq;
//  struct resource resource[DEVICE_COUNT_RESOURCE];
//  resource_size_t fw_addr[DEVICE_COUNT_RESOURCE];
//  unsigned int transparent:1;
//  unsigned int multifunction:1;
//  unsigned int is_added:1;
//  unsigned int is_busmaster:1;
//  unsigned int no_msi:1;
//  unsigned int block_ucfg_access:1;
//  unsigned int broken_parity_status:1;
//  unsigned int irq_reroute_variant:2;
//  unsigned int msi_enabled:1;
//  unsigned int msix_enabled:1;
//  unsigned int ari_enabled:1;
//  unsigned int is_managed:1;
//  unsigned int is_pcie:1;
//  unsigned int needs_freset:1;
//  unsigned int state_saved:1;
//  unsigned int is_physfn:1;
//  unsigned int is_virtfn:1;
//  unsigned int reset_fn:1;
//  unsigned int is_hotplug_bridge:1;
//  unsigned int __aer_firmware_first_valid:1;
//  unsigned int __aer_firmware_first:1;
//  pci_dev_flags_t dev_flags;
//  atomic_t enable_cnt;
//  u32 saved_config_space[16];
//  struct hlist_head saved_cap_space;
//  struct bin_attribute *rom_attr;
//  int rom_attr_enabled;
//  struct bin_attribute *res_attr[DEVICE_COUNT_RESOURCE];
//  struct bin_attribute *res_attr_wc[DEVICE_COUNT_RESOURCE];
//  struct pci_vpd *vpd;
}

/* struct bus_type pci_bus_type = { */
/*     .name       = "pci", */
/* //  .match      = pci_bus_match, */
/* //  .uevent     = pci_uevent, */
/* //  .probe      = pci_device_probe, */
/* //  .remove     = pci_device_remove, */
/* //  .shutdown   = pci_device_shutdown, */
/* //  .dev_attrs  = pci_dev_attrs, */
/* //  .bus_attrs  = pci_bus_attrs, */
/* //  .pm     = PCI_PM_OPS_PTR, */
/* }; */

global bus_type pci_bus_type;
/* pci_bus_type.name       = "pci"; */

/****************************************************************************/

/**
 * get_driver - increment driver reference count.
 * @drv: driver.
 */
/* struct device_driver *get_driver(struct device_driver *drv) { */
/*  //  if (drv) { */
/*  //      struct device_driver *a; */
/*  //      return a; */
/*  //  } */
/*  return NULL; */
/* } */

device_driver get_driver(device_driver drv)
  requires true
  ensures res=null;
{
  //  if (drv) {
  //      struct device_driver *a;
  //      return a;
  //  }
  return null;
}

/**
 * put_driver - decrement driver's refcount.
 * @drv: driver.
 */
/* void put_driver(struct device_driver *drv) { */
/*  return; */
/* } */


void put_driver(device_driver drv)
  requires true
  ensures true;
{
  return;
}

/**
 * driver_attach - try to bind driver to devices.
 * @drv: driver.
 *
 * Walk the list of devices that the bus has on it and try to
 * match the driver with each one.  If driver_probe_device()
 * returns 0 and the @dev->driver is set, we've found a
 * compatible pair.
 */
/* int driver_attach(struct device_driver *drv) { */
/*  return 0; */
/* } */

int driver_attach(device_driver drv)
  requires true
  ensures res=0;
{
    return 0;
}

void prefetch()
  requires true
  ensures true;
{
    return;
}

/**
 * driver_register - register driver with bus
 * @drv: driver to register
 *
 * We pass off most of the work to the bus_add_driver() call,
 * since most of the things we have to do deal with the bus
 * structures.
 */
int driver_register( device_driver drv )
  requires drv::device_driver<n,b,o,m>
  ensures drv::device_driver<n,b,o,m>;
{
    int a;
    return a;
}

/**
 * driver_unregister - remove driver from system.
 * @drv: driver.
 *
 * Again, we pass off most of the work to the bus-level call.
 */
void driver_unregister(device_driver drv)
  requires drv::device_driver<n,b,o,m>
  ensures drv::device_driver<n,b,o,m>;
{
    return;
}

/****************************************************************************/
pred_prim RS_mem<i:int>
 inv i>0 & self!=null;

RS_mem malloc(int n)
 requires n>0
 ensures  res=null or res::RS_mem<n>;

pci_dynid cast_to_pci_dynid_ptr(RS_mem p)
 case {
  p=null -> ensures res=null;
  p!=null -> 
    requires p::RS_mem<a> //& a>=size(item)
    ensures res::pci_dynid<n,id> * n::list_head<_,_> * id::pci_device_id<_,_,_,_,_,_,_,_>;
 }

/**
 * pci_add_dynid - add a new PCI device ID to this driver and re-probe devices
 * @drv: target pci driver
 * @vendor: PCI vendor ID
 * @device: PCI device ID
 * @subvendor: PCI subvendor ID
 * @subdevice: PCI subdevice ID
 * @class: PCI class
 * @class_mask: PCI class mask
 * @driver_data: private driver data
 *
 * Adds a new dynamic pci device ID to this driver and causes the
 * driver to probe for all devices again.  @drv must have been
 * registered prior to calling this function.
 *
 * CONTEXT:
 * Does GFP_KERNEL allocation.
 *
 * RETURNS:
 * 0 on success, -errno on failure.
 */
/*
 int pci_add_dynid(struct pci_driver *drv, unsigned int vendor, 
        unsigned int device, unsigned int subvendor, unsigned int subdevice, 
        unsigned int class, unsigned int class_mask, unsigned long driver_data) { 
    struct pci_dynid *dynid; 
    int retval; 

    dynid = (struct pci_dynid *) malloc(sizeof(struct pci_dynid)); 
    if (!dynid) 
        return -12; 

    dynid->id.vendor = vendor; 
    dynid->id.device = device; 
    dynid->id.subvendor = subvendor; 
    dynid->id.subdevice = subdevice; 
    dynid->id.class = class; 
    dynid->id.class_mask = class_mask; 
    dynid->id.driver_data = driver_data; 

    list_add_tail(&dynid->node, &drv->dynids.list); 

    get_driver(&drv->driver); 
    retval = driver_attach(&drv->driver); 
    put_driver(&drv->driver); 

    return retval; 
 } 
*/
int pci_add_dynid(pci_driver drv, int vendor,
        int device, int subvendor, int subdevice,
        int class_, int class_mask, int driver_data)
  infer [H]
  requires drv::pci_driver<node1,_,_,d,dy> * dy::pci_dynids<head1> 
            * prev::list_head<head1,_> * head1::dllN<prev,size> 
            * node1::list_head<_,_> * d::device_driver<_,_,_,_> & H(size)
  ensures true;
 {
    pci_dynid dynid;
    int retval;

    dynid = cast_to_pci_dynid_ptr (malloc(1));
    if (dynid==null)
        return -12;

    dynid.id.vendor = vendor;
    dynid.id.device = device;
    dynid.id.subvendor = subvendor;
    dynid.id.subdevice = subdevice;
    dynid.id.class_ = class_;
    dynid.id.class_mask = class_mask;
    dynid.id.driver_data = driver_data;

    list_add_tail(dynid.node, drv.dynids.list);

    get_driver(drv.driver);
    retval = driver_attach(drv.driver);
    put_driver(drv.driver);

    return retval;
}

/* static void pci_free_dynids(struct pci_driver *drv) */
/* { */
/*     struct pci_dynid *dynid, *n; */

/*     dynid = (struct pci_dynid *) (&drv->dynids.list)->next; */
/*     n = (struct pci_dynid *) dynid->node.next; */
/*     while (&dynid->node != (&drv->dynids.list)) { */
/*         list_del(&dynid->node); */
/*         free(dynid); */
/*         dynid = n; */
/*         n = (struct pci_dynid *) n->node.next; */
/*     } */
/*     return; */
/* } */

pci_dynid cast_to_pci_dynid1 (list_head p)
  requires p::cllN<prev,start,size>
  ensures res::pci_dynid<p,id> * p::cllN<prev,start,size> * id::pci_device_id<_,_,_,_,_,_,_,_>;

void pci_free_dynids_loop(pci_driver drv, ref pci_dynid dynid, ref pci_dynid n)
  requires drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
           dynid::pci_dynid<node1,id1> * n::pci_dynid<next1,id2> *
           prev1::list_head<node1,prev2> * node1::list_head<next1,prev1> * 
           next1::list_head<next2,node1> * next2::cllN<next1,prev1,size>
  case {
   node1 = head1 ->
    ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
            dynid'::pci_dynid<node1,id1> * n'::pci_dynid<next1,id2> *
            prev1::list_head<node1,prev2> * node1::list_head<next1,prev1> * 
            next1::list_head<next2,node1> * next2::cllN<next1,prev1,size>;
   node1 != head1 ->
    case{
     next1 = head1 ->
      ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
              dynid'::pci_dynid<node1,id1> * n'::pci_dynid<next1,id2> *
              prev1::list_head<node1,prev2> * node1::list_head<next1,prev1> * 
              next1::list_head<next2,node1> * next2::cllN<next1,prev1,size>;
     next1 != head1 ->
      case{
       next2 = prev1 ->
        ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
                dynid'::pci_dynid<next1,id2> * n'::pci_dynid<prev1,id3>  *
                prev1::list_head<next1,prev2> * node1::list_head<null,null> * 
                next1::list_head<prev1,prev1> * id3::pci_device_id<_,_,_,_,_,_,_,_>;
       next2 != prev1 ->
        ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
                dynid'::pci_dynid<next1,id2> * n'::pci_dynid<next3,id3> *
                prev1::list_head<next1,prev2> * node1::list_head<null,null> * 
                next1::list_head<next3,prev1> * next3::cllN<next1,prev1,size> *
                id3::pci_device_id<_,_,_,_,_,_,_,_> ;
      }
    }
  }

relation Q2(int a, int b).
relation Q3(int a, int b).
void pci_free_dynids_loop_1(pci_driver drv, ref pci_dynid dynid, ref pci_dynid n)
  infer [P,Q1,Q2,Q3]
  requires drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
           dynid::pci_dynid<node1,id1> * n::pci_dynid<next1,id2> *
           prev1::list_head<node1,prev2> * node1::list_head<next1,prev1> * 
           next1::list_head<next2,node1> * next2::cllN<next1,prev1,size> & P(size)
  case {
   node1 = head1 ->
    ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
            dynid'::pci_dynid<node1,id1> * n'::pci_dynid<next1,id2> *
            prev1::list_head<node1,prev2> * node1::list_head<next1,prev1> * 
            next1::list_head<next2,node1> * next2::cllN<next1,prev1,size1> & Q1(size1,size);
   node1 != head1 ->
    case{
     next1 = head1 ->
      ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
              dynid'::pci_dynid<node1,id1> * n'::pci_dynid<next1,id2> *
              prev1::list_head<node1,prev2> * node1::list_head<next1,prev1> * 
              next1::list_head<next2,node1> * next2::cllN<next1,prev1,size2> & Q2(size,size2);
     next1 != head1 ->
      case{
       next2 = prev1 ->
        ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
                dynid'::pci_dynid<next1,id2> * n'::pci_dynid<prev1,id3>  *
                prev1::list_head<next1,prev2> * node1::list_head<null,null> * 
                next1::list_head<prev1,prev1> * id3::pci_device_id<_,_,_,_,_,_,_,_>;
       next2 != prev1 ->
        ensures drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
                dynid'::pci_dynid<next1,id2> * n'::pci_dynid<next3,id3> *
                prev1::list_head<next1,prev2> * node1::list_head<null,null> * 
                next1::list_head<next3,prev1> * next3::cllN<next1,prev1,size3> *
                id3::pci_device_id<_,_,_,_,_,_,_,_> & Q3(size3,size);
      }
    }
  }
{
  if (dynid.node != (drv.dynids.list))
    if (dynid.node.next != (drv.dynids.list)){
      list_del(dynid.node);
      //dynid=null;
      dynid = n;
      n = cast_to_pci_dynid1(n.node.next);
      if (dynid.node.next != n.node)
        pci_free_dynids_loop_1(drv,dynid,n);
    }
}

void pci_free_dynids(pci_driver drv)
  requires drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<node1,prev2> * node1::list_head<next1,head1> * 
           next1::list_head<next2,node1> * next2::cllN<next1,head1,size>
  ensures true;

void pci_free_dynids_1(pci_driver drv)
  infer [P]
  requires drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<node1,prev2> * node1::list_head<next1,head1> * 
           next1::list_head<next2,node1> * next2::cllN<next1,head1,size> & P(size)
  ensures true;
{
    pci_dynid dynid, n;

    dynid = cast_to_pci_dynid1(drv.dynids.list.next);
    n = cast_to_pci_dynid1(dynid.node.next);
    return pci_free_dynids_loop(drv,dynid,n);
}

/**
 * pci_match_one_device - Tell if a PCI device structure has a matching
 *                        PCI device id structure
 * @id: single PCI device id structure to match
 * @dev: the PCI device structure to match against
 *
 * Returns the matching pci_device_id structure or %NULL if there is no match.
 */
/*
 static inline const struct pci_device_id * 
 pci_match_one_device(const struct pci_device_id *id, const struct pci_dev *dev) 
 { 
     if ((id->vendor == (~0) || id->vendor == dev->vendor) && 
         (id->device == (~0) || id->device == dev->device) && 
         (id->subvendor == (~0) || id->subvendor == dev->subsystem_vendor) && 
         (id->subdevice == (~0) || id->subdevice == dev->subsystem_device) && 
         !((id->class ^ dev->class) & id->class_mask)) 
         return id; 
     return NULL; 
 }
*/ 

pci_device_id
pci_match_one_device( pci_device_id id, pci_dev dev, int UNIT_MAX)
  requires id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
           dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  case {
   v1!=UNIT_MAX -> 
    case {
     v1=v2 ->
      case {
       d1!=UNIT_MAX ->
        case {
         d1=d2 -> 
          case {
           subv1!=UNIT_MAX -> 
            case {
             subv1=subv2 -> 
              case {
               subd1!=UNIT_MAX -> 
                case{
                 subd1=subd2  -> ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
                 subd1!=subd2 -> ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
                }
               subd1=UNIT_MAX -> ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
              }
             subv1!= subv2    -> ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
            }
           subv1=UNIT_MAX -> 
            case {
             subd1!=UNIT_MAX -> 
              case{
               subd1=subd2 ->    ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
               subd1!=subd2 ->   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
              }
             subd1=UNIT_MAX ->   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
            }
          }
         d1!=d2 ->               ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
        }
       d1=UNIT_MAX -> 
        case {
         subv1!=UNIT_MAX -> 
          case {
           subv1=subv2 -> 
            case {
             subd1!=UNIT_MAX -> 
              case{
               subd1=subd2 ->    ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
               subd1!=subd2 ->   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
              }
             subd1=UNIT_MAX ->   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
            }
           subv1!= subv2 ->      ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
          }
         subv1=UNIT_MAX -> 
          case {
           subd1!=UNIT_MAX -> 
            case{
             subd1=subd2 ->      ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
             subd1!=subd2 ->     ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
            }
           subd1=UNIT_MAX ->     ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
          }
        }
      }
     v1!=v2 ->                   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
    }
   v1=UNIT_MAX -> 
    case {
     d1!=UNIT_MAX ->
      case {
       d1=d2 -> 
        case {
         subv1!=UNIT_MAX -> 
          case {
           subv1=subv2 -> 
            case {
             subd1!=UNIT_MAX -> 
              case{
               subd1=subd2 ->    ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
               subd1!=subd2 ->   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
              }
             subd1=UNIT_MAX ->   ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
            }
           subv1!= subv2 ->      ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
          }
         subv1=UNIT_MAX -> 
          case {
           subd1!=UNIT_MAX -> 
            case{
             subd1=subd2 ->      ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
             subd1!=subd2 ->     ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
            }
           subd1=UNIT_MAX ->     ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
          }
        }
       d1!=d2 ->                 ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
      }
     d1=UNIT_MAX -> 
      case {
       subv1!=UNIT_MAX -> 
        case {
         subv1=subv2 -> 
          case {
           subd1!=UNIT_MAX -> 
            case{
             subd1=subd2 ->      ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
             subd1!=subd2 ->     ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
            }
           subd1=UNIT_MAX ->     ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
          }
         subv1!= subv2 ->        ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
        }
       subv1=UNIT_MAX -> 
        case {
         subd1!=UNIT_MAX -> 
          case{
           subd1=subd2 ->        ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
           subd1!=subd2 ->       ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
          }
         subd1=UNIT_MAX ->       ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
                                         dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
        }
      }
    }
  }
{
    if ((id.vendor == UNIT_MAX  || id.vendor == dev.vendor) &&
        (id.device == UNIT_MAX || id.device == dev.device) &&
        (id.subvendor == UNIT_MAX || id.subvendor == dev.subsystem_vendor) &&
        (id.subdevice == UNIT_MAX || id.subdevice == dev.subsystem_device) /* && */
        /* !((id.class_ ^ dev.class_) & id.class_mask) */)
        return id;
    return null;
}

/**
 * pci_match_id - See if a pci device matches a given pci_id table
 * @ids: array of PCI device id structures to search in
 * @dev: the PCI device structure to match against.
 *
 * Used by a driver to check whether a PCI device present in the
 * system is in its list of supported devices.  Returns the matching
 * pci_device_id structure or %NULL if there is no match.
 *
 * Deprecated, don't use this as it will not catch any dynamic ids
 * that a driver might want to check for.
 */
/*
 const struct pci_device_id *pci_match_id(const struct pci_device_id *ids, 
                      struct pci_dev *dev) 
 { 
     if (ids) { 
         while (ids->vendor || ids->subvendor || ids->class_mask) { 
             if (pci_match_one_device(ids, dev)) 
                 return ids; 
             ids++; 
         } 
     } 
     return NULL; 
 } 
*/

/* view for a singly linked list */
id_list<> == self = null
	or self::pci_device_id<_,_,_,_,_,_,_,n> * n::id_list<>
  inv true;

id_listN<size> == self = null & size=0
	or self::pci_device_id<_,_,_,_,_,_,_,n> * n::id_listN<size-1>
  inv size>=0;

pci_device_id pci_match_id(pci_device_id ids,
                      pci_dev dev)
  requires ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_> * 
          dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>;

pci_device_id pci_match_id_1(pci_device_id ids,
                      pci_dev dev)
  infer [P]
  requires ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & P(size1)
  ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_> * 
          dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>;
{
  if (ids!=null) {
    if (ids.vendor!=0 || ids.subvendor!=0 || ids.class_mask!=0) {
      if (pci_match_one_device(ids,dev,4294967295) != null)
        return ids;
      else {      
        return pci_match_id_1(ids.next,dev);
      }
    }
    return pci_match_id_1(ids.next,dev);
  }
  return null;
}

pci_device_id
pci_match_one_device_simp( pci_device_id id, pci_dev dev)
  requires id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
           dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  case{
   v1!=v2 ->
    ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
            dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=null;
   v1=v2 ->
    ensures id::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> * 
            dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & res=id;
  }
{
    if (id.vendor == dev.vendor)
        return id;
    return null;
}

pci_device_id pci_match_id_simp(pci_device_id ids,
                      pci_dev dev)
  requires ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  ensures res=null or res::pci_device_id<v1,_,_,_,_,_,_,_> * 
                      dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & v1=v2;

pci_device_id pci_match_id_simp_1(pci_device_id ids,
                      pci_dev dev)
  infer [P]
  requires ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & P(size1)
  ensures res=null or res::pci_device_id<v1,_,_,_,_,_,_,_> * 
                      dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & v1=v2;
{
  if (ids!=null) {
    if (ids.vendor!=0){
      if (pci_match_one_device_simp(ids,dev)!=null)
        return ids;
      else {
        return pci_match_id_simp_1(ids.next,dev);
      }
    }
    return pci_match_id_simp_1(ids.next,dev);
  }
  return null;
}

/**
 * pci_match_device - Tell if a PCI device structure has a matching PCI device id structure
 * @drv: the PCI driver to match against
 * @dev: the PCI device structure to match against
 *
 * Used by a driver to check whether a PCI device present in the
 * system is in its list of supported devices.  Returns the matching
 * pci_device_id structure or %NULL if there is no match.
 */

/*static const struct pci_device_id *pci_match_device(struct pci_driver *drv,*/
/*                            struct pci_dev *dev)*/
/*{*/
/*    struct pci_dynid *dynid;*/

/*    /* Look at the dynamic ids first, before the static ones */*/
/*    dynid = (struct pci_dynid *) (&drv->dynids.list)->next;*/
/*    while (1) {*/
/*        prefetch((void *) dynid->node.next);*/
/*        if (&dynid->node == (&drv->dynids.list)){*/
/*            break;*/
/*        }*/
/*        if (pci_match_one_device(&dynid->id, dev)) {*/
/*            return &dynid->id;*/
/*        }*/
/*        dynid = (struct pci_dynid *) dynid->node.next;*/
/*    }*/
/*    return pci_match_id(drv->id_table, dev);*/
/*}*/
pci_device_id pci_match_device_loop_simp(pci_driver drv, ref pci_dynid dynid,
                             pci_dev dev)
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           ids::id_listN<size1> * id1::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> *
           dynid::pci_dynid<node1,id1> * node1::cllN<_,head1,_> * 
           dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  case {
   head1=null ->
    ensures res=null;
   head1!=null ->
    case {
     node1=head1 ->
      ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
     node1!=head1 ->
      case {
       v1=v2 ->
        ensures res::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n>;
       v1!=v2 ->        
        ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
      }
    }
  }

relation P1(int a, int b).
pci_device_id pci_match_device_loop_simp_1(pci_driver drv, ref pci_dynid dynid,
                             pci_dev dev)
  infer [P1]
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           ids::id_listN<size1> * id1::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> *
           dynid::pci_dynid<node1,id1> * node1::cllN<_,head1,size> * 
           dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & P1(size,size1)
  case {
   head1=null ->
    ensures res=null;
   head1!=null ->
    case {
     node1=head1 ->
      ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
     node1!=head1 ->
      case {
       v1=v2 ->
        ensures res::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n>;
       v1!=v2 ->        
        ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
      }
    }
  }
{
  if (drv.dynids.list == null){
    return null;
  }
  if (dynid.node == drv.dynids.list){
    return pci_match_id_simp(drv.id_table,dev);
  }
  if (dynid.id.vendor==dev.vendor) {
    return dynid.id;
  }
  dynid=cast_to_pci_dynid1(dynid.node.next);
  return pci_match_device_loop_simp_1(drv,dynid,dev);

}

pci_device_id pci_match_device_simp(pci_driver drv,
                             pci_dev dev)
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<head1,next1> * next1::cllN<head1,head1,size> *
           ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;

pci_device_id pci_match_device_simp_1(pci_driver drv,
                             pci_dev dev)
  infer [P1]
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<head1,next1> * next1::cllN<head1,head1,size> *
           ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & P1(size,size1)
  ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
{
    pci_dynid dynid;

    /* Look at the dynamic ids first, before the static ones */
    dynid = cast_to_pci_dynid1 (drv.dynids.list.next);
    return pci_match_device_loop_simp(drv,dynid,dev);
}

pci_device_id pci_match_device_loop(pci_driver drv, ref pci_dynid dynid,
                             pci_dev dev)
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           ids::id_listN<size1> * id1::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> *
           dynid::pci_dynid<node1,id1> * node1::cllN<_,head1,size> * 
           dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  case {
   head1=null ->
    ensures res=null;
   head1!=null ->
    case {
     node1=head1 ->
      ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
     node1!=head1 ->
      ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
    }
  }

pci_device_id pci_match_device_loop_1(pci_driver drv, ref pci_dynid dynid,
                             pci_dev dev)
  infer [P1]
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           ids::id_listN<size1> * id1::pci_device_id<v1,d1,subv1,subd1,cl1,clm,dd,n> *
           dynid::pci_dynid<node1,id1> * node1::cllN<_,head1,size> * 
           dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & P1(size,size1)
  case {
   head1=null ->
    ensures res=null;
   head1!=null ->
    case {
     node1=head1 ->
      ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
     node1!=head1 ->
      ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
    }
  }
{

  if (drv.dynids.list == null){
    return null;
  }
  if (dynid.node == (drv.dynids.list)){
    return pci_match_id(drv.id_table,dev);
  }
  if (pci_match_one_device(dynid.id,dev,4294967295) != null) {
    return dynid.id;
  }
  dynid=cast_to_pci_dynid1(dynid.node.next);
  return pci_match_device_loop_1(drv,dynid,dev);

}

pci_device_id pci_match_device(pci_driver drv,
                             pci_dev dev)
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<head1,next1> * next1::cllN<head1,head1,size> *
           ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc>
  ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;

pci_device_id pci_match_device_1(pci_driver drv,
                             pci_dev dev)
  infer [P1]
  requires drv::pci_driver<no,na,ids,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<head1,next1> * next1::cllN<head1,head1,size> *
           ids::id_listN<size1> * dev::pci_dev<v2,d2,subv2,subd2,cl2,dvc> & P1(size,size1)
  ensures res=null or res::pci_device_id<_,_,_,_,_,_,_,_>;
{
    pci_dynid dynid;

    /* Look at the dynamic ids first, before the static ones */
    dynid = cast_to_pci_dynid1 (drv.dynids.list.next);
    return pci_match_device_loop(drv,dynid,dev);
}

int pci_create_newid_file(pci_driver drv)
  requires true
  ensures res=0;
{
    return 0;
}

int pci_create_removeid_file(pci_driver drv)
  requires true
  ensures res=0;
{
    return 0;
}

void pci_remove_newid_file(pci_driver drv)
  requires true
  ensures true;
{
  return;
}

/**
 * __pci_register_driver - register a new pci driver
 * @drv: the driver structure to register
 * @owner: owner module of drv
 * @mod_name: module name string
 *
 * Adds the driver structure to the list of registered drivers.
 * Returns a negative value on error, otherwise 0.
 * If no error occurred, the driver remains registered even if
 * no device was claimed during registration.
 */
/* int __pci_register_driver(struct pci_driver *drv, struct module *owner, */
/*               const char *mod_name) */
/* { */
/*     int error; */

/*     /\* initialize common driver fields *\/ */
/*     drv->driver.name = drv->name; */
/*     drv->driver.bus = &pci_bus_type; */
/*     drv->driver.owner = owner; */
/*     drv->driver.mod_name = mod_name; */

/*     INIT_LIST_HEAD(&drv->dynids.list); */

/*     /\* register with core *\/ */
/*     error = driver_register(&drv->driver); */
/*     if (error) */
/*         goto out; */

/*     error = pci_create_newid_file(drv); */
/*     if (error) */
/*         goto out_newid; */

/*     error = pci_create_removeid_file(drv); */
/*     if (error) */
/*         goto out_removeid; */

/* out: */
/*     return error; */

/* out_removeid: */
/*     pci_remove_newid_file(drv); */
/* out_newid: */
/*     driver_unregister(&drv->driver); */
/*     goto out; */
/* } */
int __pci_register_driver(pci_driver drv, module owner,
              char mod_name)
  requires drv::pci_driver<node1,_,_,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<_,_> * d::device_driver<_,_,_,_> *
           mod_name::char<_> * owner::module<_,_>
  ensures res=0 or res!=0;
{
    int error;

    /* initialize common driver fields */
    drv.driver.name = drv.name;
    drv.driver.bus = pci_bus_type;
    drv.driver.owner = owner;
    drv.driver.mod_name = mod_name;

    INIT_LIST_HEAD(drv.dynids.list);

    /* register with core */
    error = driver_register(drv.driver);
    if (error!=0)
        return error;

    error = pci_create_newid_file(drv);
    if (error!=0){
      driver_unregister(drv.driver);
      return error;
    }

    error = pci_create_removeid_file(drv);
    if (error !=0)  {
       pci_remove_newid_file(drv);
       driver_unregister(drv.driver);
       return error;
    }
    return 0;
}

void pci_remove_removeid_file(pci_driver drv)
  requires true
  ensures true;
{
  return;
}

/**
 * pci_unregister_driver - unregister a pci driver
 * @drv: the driver structure to unregister
 *
 * Deletes the driver structure from the list of registered PCI drivers,
 * gives it a chance to clean up by calling its remove() function for
 * each device it was responsible for, and marks those devices as
 * driverless.
 */
/* void */
/* pci_unregister_driver(struct pci_driver *drv) */
/* { */
/*     pci_remove_removeid_file(drv); */
/*     pci_remove_newid_file(drv); */
/*     driver_unregister(&drv->driver); */
/*     pci_free_dynids(drv); */
/* } */
void
pci_unregister_driver(pci_driver drv)
  requires drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<node1,prev2> * node1::list_head<next1,head1> * 
           next1::list_head<next2,node1> * next2::cllN<next1,head1,size> *
           d::device_driver<_,_,_,_>
  ensures true;

void
pci_unregister_driver_1(pci_driver drv)
  infer [P]
  requires drv::pci_driver<no,na,id,d,dy> * dy::pci_dynids<head1> *
           head1::list_head<node1,prev2> * node1::list_head<next1,head1> * 
           next1::list_head<next2,node1> * next2::cllN<next1,head1,size> *
           d::device_driver<_,_,_,_> & P(size)
  ensures true;
{
    pci_remove_removeid_file(drv);
    pci_remove_newid_file(drv);
    driver_unregister(drv.driver);
    pci_free_dynids(drv);
}

/**
 * pci_bus_match - Tell if a PCI device structure has a matching PCI device id structure
 * @dev: the PCI device structure to match against
 * @drv: the device driver to search for matching PCI device id structures
 *
 * Used by a driver to check whether a PCI device present in the
 * system is in its list of supported devices. Returns the matching
 * pci_device_id structure or %NULL if there is no match.
 */
/* static int pci_bus_match(struct device *dev, struct device_driver *drv) */
/* { */
/*     struct pci_dev *pci_dev = (struct pci_dev *) dev; */
/*     struct pci_driver *pci_drv = (struct pci_driver *) drv; */
/*     const struct pci_device_id *found_id; */

/*     found_id = pci_match_device(pci_drv, pci_dev); */
/*     if (found_id) */
/*         return 1; */

/*     return 0; */
/* } */

pci_dev to_pci_dev(device dev)
  requires dev::device<_>
  ensures res::pci_dev<_,_,_,_,_,dev>;

pci_driver to_pci_driver(device_driver drv)
  requires drv::device_driver<_,_,_,_>
  ensures res::pci_driver<_,_,ids,drv,dy> * dy::pci_dynids<head1> *
          head1::list_head<head1,next1> * next1::cllN<head1,head1,size> * 
          drv::device_driver<_,_,_,_> * ids::id_listN<size1>;

int pci_bus_match(device dev, device_driver drv)
  requires drv::device_driver<_,_,_,_> * dev::device<_>
  ensures res=0 or res=1;
{
    pci_dev pci_dev = to_pci_dev(dev);
    pci_driver pci_drv = to_pci_driver(drv);
    pci_device_id found_id;

    found_id = pci_match_device(pci_drv, pci_dev);
    if (found_id != null)
        return 1;

    return 0;
}

