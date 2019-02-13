#include <pins2lts-sym/alg/aux.h>
#include <hre/feedback.h>
#include <stdbool.h>
#include <hre/user.h>
#include "frame.h"
#include "pdr-util.h"


frame *
frame_empty()
{
    frame *f = RTmallocZero (sizeof(frame));
    f->states = empty();
    return f;
}

frame *
frame_create(vset_t S)
{
    frame *f = frame_empty();
    vset_copy(f->states, S);
    return f;
}

bool
frame_is_initial(frame *f)
{
    return f->prev == NULL;
}

void
insert_before(frame *list, frame *new)
{
    new->next = list;
    new->prev = list->prev;

    if (new->prev != NULL) {
        new->prev->next = new;
    }
    new->next->prev = new;
}

void
insert_after(frame *list, frame *new)
{
    new->next = list->next;
    new->prev = list;

    new->prev->next = new;
    if (new->next != NULL) {
        new->next->prev = new;
    }
}

void
print_frame_sizes(frame *frame)
{
    struct frame *f = frame;

    int i = 0;
    while (f->prev != NULL) {
        Warning(info, "[print_frame_sizes] frame %d size:", i);
        vset_count_info(f->states);
        f = f->prev;
        i++;
    }
}