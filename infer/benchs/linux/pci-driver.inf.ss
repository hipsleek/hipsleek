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

dll<q> == self::list_head<self , q>
  or self::list_head<p , q> * p::dll<self> 
  inv self!=null;

dll_size<q,n> == self::list_head<self , q> & n=1
  or self::list_head<p , q> * p::dll_size<self,n-1>
  inv self!=null & n>=1;

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
/*
 static inline __attribute__((always_inline)) void list_add_tail( 
        struct list_head *new, struct list_head *head) { 
    __list_add(new, head->prev, head); 
 } 
*/
relation D(int a, int b).
void list_add_tail(list_head new1, list_head head1)
  infer [D]
  requires new1::list_head<_,_> * prev::list_head<head1,f> * head1::dll_size<prev,n>
  ensures prev::list_head<new1,f> * new1::list_head<head1,prev> * head1::dll_size<new1,m> & D(n,m);
{
  __list_add(new1, head1.prev, head1);
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
}

/* struct pci_dynid { */
/*  struct list_head node; */
/*  struct pci_device_id id; */
/* }; */

data pci_dynid {
    list_head node;
    pci_device_id id;
}

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
    ensures res::pci_dynid<n,id> * n::list_head<_,_> * id::pci_device_id<_,_,_,_,_,_,_>;
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

/* struct device_driver { */
/*  const char *name; */
/*  struct bus_type *bus; */
/*  //  int (*probe)(struct device *dev); */
/*  //  int (*remove)(struct device *dev); */
/* }; */

data device_driver {
    char name;
    bus_type bus;
    //  int (*probe)(struct device *dev);
    //  int (*remove)(struct device *dev);
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

/****************************************************************************/

/**
 * get_driver - increment driver reference count.
 * @drv: driver.
 */
/*TODO*/
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
/*TODO*/
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
/*TODO*/
/* int driver_attach(struct device_driver *drv) { */
/*  return 0; */
/* } */

int driver_attach(device_driver drv)
  requires true
  ensures res=0;
{
    return 0;
}
/****************************************************************************/

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
  requires drv::pci_driver<node1,_,_,d,dy> * dy::pci_dynids<head1> 
            * prev::list_head<head1,_> * head1::dll_size<prev,_>
            * node1::list_head<_,_> * d::device_driver<_,_>
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

