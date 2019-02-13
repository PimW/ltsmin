#ifndef PINS2LTS_SYM_FRAME_H
#define PINS2LTS_SYM_FRAME_H

/*
 * Frame linked list structure and operations
 */
typedef struct frame
{
    vset_t states;
    struct frame* next;
    struct frame* prev;
} frame;

frame *frame_create(vset_t S);
frame *frame_empty();
bool frame_is_initial(frame *f);
void insert_before(frame *list, frame *new);
void insert_after(frame *list, frame *new);
void print_frame_sizes(frame *frame);

#endif //PINS2LTS_SYM_FRAME_H
