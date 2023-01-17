#include <lean/lean.h>

typedef struct {
    lean_object *data, *finalizer;
} resource;

static void resource_finalize(void *data) {
    resource *resource = data;
    lean_dec(lean_apply_1(resource->finalizer, resource->data));
    free(resource);
}

static void resource_foreach(void *data, b_lean_obj_arg f) {
    resource *resource = data;
    lean_inc(f);
    lean_inc(resource->data);
    lean_dec(lean_apply_1(f, resource->data));
    lean_inc(f);
    lean_inc(resource->finalizer);
    lean_dec(lean_apply_1(f, resource->finalizer));
}

static lean_external_class *resource_class;

LEAN_EXPORT lean_obj_res lean_resource_mk(lean_obj_arg data, lean_obj_arg finalizer) {
    resource *resource = malloc(sizeof *resource);
    resource->data = data;
    resource->finalizer = finalizer;
    if (!resource_class) {
        resource_class = lean_register_external_class(resource_finalize, resource_foreach);
    }
    return lean_alloc_external(resource_class, resource);
}

LEAN_EXPORT lean_obj_res lean_resource_data(b_lean_obj_arg data) {
    resource *resource = lean_get_external_data(data);
    lean_inc(resource->data);
    return resource->data;
}
