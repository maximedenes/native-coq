/* -------------------------------------------------------------------- */
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>

#include <fcntl.h>
#include <unistd.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/callback.h>

#define DEBUG 1

/* -------------------------------------------------------------------- */
#define NEW(T)  ((T*) malloc(sizeof (T)))
#define FREE(P) (free(P))

/* -------------------------------------------------------------------- */
typedef struct resource {
     int  fd;
  uint8_t *contents;
  size_t  size;
} resource_t;

/* -------------------------------------------------------------------- */
static int resource_create_from_fd(int fd, resource_t *out) {
  struct stat st;

  memset(out, 0, sizeof(resource_t));

  if (fstat(fd, &st) < 0)
    goto bailout;

  out->contents = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  out->size     = st.st_size;
  out->fd       = fd;

  if (out->contents == MAP_FAILED)
    goto bailout;

  return 0;

 bailout:
  if (out->contents != NULL) {
    if (out->contents != MAP_FAILED)
      (void) munmap(out->contents, out->size);
  }
  return -1;
}

/*-------------------------------------------------------------------- */
static int resource_create_from_filename(const char *filename, resource_t *out) {
  int fd = -1;

  if ((fd = open(filename, O_RDONLY)) < 0)
    goto bailout;
  if (resource_create_from_fd(fd, out) < 0)
    goto bailout;

  return 0;

 bailout:
  if (fd >= 0)
    (void) close(fd);
  return -1;
}

/* -------------------------------------------------------------------- */
static void resource_release(resource_t *out) {
  if (out->fd >= 0)
    (void) close(out->fd);
  if (out->contents && out->contents != MAP_FAILED)
    (void) munmap(out->contents, out->size);
}

/* -------------------------------------------------------------------- */
static int resource_check_offset(const resource_t *the   ,
                                 /*-*/ size_t      offset,
                                 /*-*/ size_t      length)
{
  return
    (   length < the->size
     && offset < the->size - length);
}

/* -------------------------------------------------------------------- */
#define Resource_val(v) (*((resource_t **) Data_custom_val(v)))

/* -------------------------------------------------------------------- */
static void caml_resource_finalize(value data) {
  if (Resource_val(data) != NULL)
    resource_release(Resource_val(data));
}

/* -------------------------------------------------------------------- */
static struct custom_operations resource_ops = {
  "fr.inria.native-coq.resource",
  caml_resource_finalize,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
};

/* -------------------------------------------------------------------- */
static value caml_alloc_resource(void) {
  value resource;

  resource = alloc_custom(&resource_ops, sizeof (resource_t*), 0, 1);
  Resource_val(resource) = NULL;

  return resource;
}

/* -------------------------------------------------------------------- */
#define EXN_INVALID_RESOURCE "fr.inria.native-coq.resource.exn.InvalidResource"

static void caml_raise_invalid_resource(void) {
  caml_raise_constant(*caml_named_value(EXN_INVALID_RESOURCE));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_resource_from_filename(value filename) {
  CAMLparam1(filename);

  resource_t *resource = NULL;
  value mlresource = 0;

  mlresource = caml_alloc_resource();

  if ((resource = NEW(resource_t)) == NULL) {
    FREE(resource);
    caml_raise_out_of_memory(); /* no-return */
  }

  if (resource_create_from_filename(String_val(filename), resource) < 0) {
    FREE(resource);
    caml_raise_invalid_resource(); /* no-return */
  }

  Resource_val(mlresource) = resource;

#if DEBUG
  (void) fprintf(stderr, "resource [%lx] created from %s\n",
                 (size_t) resource->contents,
                 String_val(filename));
#endif

  CAMLreturn(mlresource);
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_resource_release(value mlresource) {
  CAMLparam1(mlresource);

  if (Resource_val(mlresource) != NULL) {
    resource_release(Resource_val(mlresource));
    Resource_val(mlresource) = NULL;
  }

  CAMLreturn(Val_unit);
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_resource_length(value mlresource) {
  CAMLparam1(mlresource);

  if (Resource_val(mlresource) == NULL)
    caml_raise_invalid_resource(); /* no-return */

  CAMLreturn(caml_copy_int64(Resource_val(mlresource)->size));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_resource_get1(value mlresource, value mloffset) {
  CAMLparam2(mlresource, mloffset);

  resource_t *resource = NULL;
  size_t offset = 0u;

#if DEBUG
  (void) fprintf(stderr, "entering [caml_resource_get1]\n");
#endif

  if ((resource = Resource_val(mlresource)) == NULL)
    caml_raise_invalid_resource(); /* no-return */

  offset = Int_val(mloffset);

#if DEBUG
  (void) fprintf(stderr, "caml_resource_get1[%lx/%lu]\n",
                 (size_t) resource->contents, offset);
#endif

  if (offset < 0 || offset >= resource->size) {
    /* no-return */
    caml_invalid_argument("resource.get1: invalid offset");
  }

#if DEBUG
  (void) fprintf(stderr, "caml_resource_get1[%lx/%lu] = %x\n",
                 (size_t) resource->contents, offset,
                 (uint8_t) resource->contents[offset]);
#endif

  CAMLreturn(Int_val(resource->contents[offset]));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_resource_le32(value mlresource, value mloffset) {
  CAMLparam1(mlresource);

  resource_t *resource = NULL;
  int offset = 0u;

  if ((resource = Resource_val(mlresource)) == NULL)
    caml_raise_invalid_resource(); /* no-return */
  offset = Int_val(mloffset);

  if (offset < 0) {
    /* no-return */
    caml_invalid_argument("resource.le32: negative offset");
  }

  if (!resource_check_offset(resource, offset, sizeof(uint32_t))) {
    /* no-return */
    caml_invalid_argument("resource.le32: invalid offset");
  }

  uint32_t aout =
      ((uint32_t) resource->contents[offset+3] << 24)
    | ((uint32_t) resource->contents[offset+2] << 16)
    | ((uint32_t) resource->contents[offset+1] <<  8)
    | ((uint32_t) resource->contents[offset+0] <<  0);

  if ((aout & 0x80000000))
    caml_failwith("resource.le32: read integer too large");

  CAMLreturn((int32_t) Int_val(aout));
}

/* -------------------------------------------------------------------- */
CAMLprim value caml_resource_get
  (value mlresource,
   value mloffset  ,
   value mllength  ,
   value mlout     )
{
  CAMLparam4(mlresource, mloffset, mllength, mlout);

  resource_t *resource = NULL;
  size_t length = 0u;
  size_t offset = 0u;

  if ((resource = Resource_val(mlresource)) == NULL)
    caml_raise_invalid_resource(); /* no-return */

  offset = Int_val(mloffset);
  length = Int_val(mllength);

  if (offset < 0 || length < 0) {
    /* no-return */
    caml_invalid_argument("resource.get: negative offset/length");
  }

  if (!resource_check_offset(resource, offset, length)) {
    /* no-return */
    caml_invalid_argument("resource.get: invalid offset/length");
  }

  if (caml_string_length(mlout) < length) {
    /* no-return */
    caml_invalid_argument("resource.get: out-buffer too small");
  }

  (void) memcpy(String_val(mlout), &resource->contents[offset], length);

  CAMLreturn(Val_unit);
}
