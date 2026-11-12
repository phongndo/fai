/* The types and functions shared by struct_extern.c (compiled by fai-cc) and
 * extern/struct_extern.c (compiled by the reference compiler): one of each AAPCS64 class. */
#ifndef STRUCT_EXTERN_H
#define STRUCT_EXTERN_H

struct hfa3 { float a, b, c; };                /* v0-v2 */
struct hfa4d { double a[2]; double b, c; };    /* v0-v3 */
struct small { char c; short s; int i; };      /* x0 */
struct pair { long a; const char *s; };        /* x0, x1 */
struct al16 { _Alignas(16) long a; int b; };   /* an even pair */
struct big { int v[7]; double d; };            /* by reference, x8 */
struct flags { unsigned on : 1, mode : 3; signed char lvl : 4; short id; };
union num { long l; double d; char c[8]; };
struct empty {};                               /* nothing, also through `...` */

/* Defined by the reference compiler. */
struct hfa3 ext_hfa3(struct hfa3 x, float k);
struct hfa4d ext_hfa4d(struct hfa4d x);
struct small ext_small(int pad, struct small x);
struct pair ext_pair(struct pair x, struct pair y);
struct al16 ext_al16(int pad, struct al16 x);
struct big ext_big(struct big x, long k);
struct flags ext_flags(struct flags x);
union num ext_num(union num x, int which);
struct empty ext_empty(int a, struct empty e, int b);
/* Nine of each register class, so the last ones go on the stack. */
double ext_many(struct hfa3 a, struct hfa3 b, struct hfa3 c, struct small d, struct pair e,
                struct pair f, struct pair g, struct small h, struct big i, struct hfa3 j,
                struct small k, struct pair l);
/* Reads structs through `...` as the tags say. */
long ext_va(const char *tags, ...);
/* Calls back the fai-cc functions below, directly and through the given pointers. */
long ext_callbacks(struct pair (*f)(struct pair), struct big (*g)(struct big));

/* Defined by fai-cc, called by the reference compiler's code. */
struct pair fai_pair(struct pair x);
struct big fai_big(struct big x);
struct hfa4d fai_hfa4d(struct hfa4d x, struct small s);
long fai_va(const char *tags, ...);

#endif
