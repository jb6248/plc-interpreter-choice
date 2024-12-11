#include "all.h"
/* copy.c ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) */
/* private declarations for copying collection 276a */
static Value *fromspace, *tospace; // used only at GC time
static int semispacesize;          // # of objects in fromspace or tospace
/* private declarations for copying collection 276b */
static Value *hp, *heaplimit;      // used for every allocation

// statistics
static int num_collections = 0;
static int total_objects_copied = 0;

/* private declarations for copying collection 277a */
static void copy(void);
static void scanenv      (Env env);
static void scanexp      (Exp exp);
static void scanexplist  (Explist es);
static void scanframe    (Frame *fr);
static void scantest     (UnitTest t);
static void scantests    (UnitTestlist ts);
static void scanloc      (Value *vp);
/* private declarations for copying collection 278b */
static inline bool isinspace(Value *loc, Value *space) {
    return space <= loc && loc < space + semispacesize;
}

static Value *forward(Value *p);
/* private declarations for copying collection S377e */
static void collect(void);
/* copy.c ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) */
/* representation of [[struct Stack]] S343a */
struct Stack {
    int size;
    Frame *frames;  // memory for 'size' frames
    Frame *sp;      // points to first unused frame
};
/* copy.c 276c */
int nalloc;   /* OMIT */
Value* allocloc(void) {
    if (hp == heaplimit || hp == NULL)
        collect();
    assert(isinspace(hp, fromspace)); /*runs after spaces are swapped*/ /*OMIT*/
    assert(hp < heaplimit);
    nalloc++;   /* OMIT */
    /* tell the debugging interface that [[hp]] is about to be allocated 282f */
    gc_debug_pre_allocate(hp);
    return hp++;
}
/* copy.c 277b */
static void scanenv(Env env) {
    for (; env; env = env->tl)
      { /*OMIT*/
        env->loc = forward(env->loc);
        assert(isinspace(env->loc, tospace)); /*OMIT*/
      } /*OMIT*/
}
/* copy.c 277c */
static void scanloc(Value *vp) {
    switch (vp->alt) {
    case NIL:
    case BOOLV:
    case NUM:
    case SYM:
        return;
    case PAIR:
        vp->pair.car = forward(vp->pair.car);
        vp->pair.cdr = forward(vp->pair.cdr);
        return;
    case CLOSURE:
        scanexp(vp->closure.lambda.body);
        scanenv(vp->closure.env);
        return;
    case PRIMITIVE:
        return;
    default:
        assert(0);
        return;
    }
}
/* copy.c 278a */
static Value* forward(Value *p) {
    if (isinspace(p, tospace)) {
        /* already in to space; must belong to scanned root */
        return p;
    } else {
        assert(isinspace(p, fromspace));
        /* forward pointer [[p]] and return the result 272b */
        if (p->alt == FORWARD) {
            assert(isinspace(p->forward, tospace));   /* OMIT */
            return p->forward;
        } else {
            assert(isinspace(hp, tospace)); /* there is room */   /* OMIT */

    /* tell the debugging interface that [[hp]] is about to be allocated 282f */
            gc_debug_pre_allocate(hp);
            *hp = *p;
            *p  = mkForward(hp);
                                /* overwrite *p with a new forwarding pointer */
            assert(isinspace(p->forward, tospace)); /*extra*/   /* OMIT */
            return hp++;
        }
    }
    return NULL; /* appease a stupid compiler */  /*OMIT*/
}
/* copy.c S366f */
static void scanexp(Exp e) {
    switch (e->alt) {
    /* cases for [[scanexp]] S366g */
    case LITERAL:
        scanloc(&e->literal);
        return;
    case VAR:
        return;
    case IFX:
        scanexp(e->ifx.cond);
        scanexp(e->ifx.truex);
        scanexp(e->ifx.falsex);
        return;
    /* cases for [[scanexp]] S367a */
    case WHILEX:
        scanexp(e->whilex.cond);
        scanexp(e->whilex.body);
        return;
    case BEGIN:
        scanexplist(e->begin);
        return;
    case SET:
        scanexp(e->set.exp);
        return;
    case LETX:
        scanexplist(e->letx.es);
        scanexp(e->letx.body);
        return;
    case LAMBDAX:
        scanexp(e->lambdax.body);
        return;
    case APPLY:
        scanexp(e->apply.fn);
        scanexplist(e->apply.actuals);
        return;
    /* cases for [[scanexp]] S367b */
    case BREAKX:
        return;
    case CONTINUEX:
        return;
    case RETURNX:
        scanexp(e->returnx);
        return;
    case THROW:
        scanexp(e->throw.exp);
        return;
    case TRY_CATCH:
        scanexp(e->try_catch.handler);
        scanexp(e->try_catch.body);
        return;
    case LONG_GOTO:
        scanexp(e->long_goto.exp);
        return;
    case LONG_LABEL:
        scanexp(e->long_label.body);
        return;
    case LOWERED:
        scanexp(e->lowered.before);
        scanexp(e->lowered.after);
        return;
    case LOOPBACK:
        return;
    /* cases for [[scanexp]] S368a */
    case HOLE:
        return;
    case ENV:
        scanenv(e->env.contents);
        return;
    }
    assert(0);
}
/* copy.c S368b */
static void scanframe(Frame *fr) {
    scanexp(&fr->form);
    if (fr->syntax != NULL)
        scanexp(fr->syntax);
}
/* copy.c S368c */
static void scanexplist(Explist es) {
    for (; es; es = es->tl)
        scanexp(es->hd);
}
/* copy.c S368d */
static void scantests(UnitTestlist tests) {
    for (; tests; tests = tests->tl)
        scantest(tests->hd);
}
/* copy.c S368e */
static void scantest(UnitTest t) {
    switch (t->alt) {
    case CHECK_EXPECT:
        scanexp(t->check_expect.check);
        scanexp(t->check_expect.expect);
        return;
    case CHECK_ASSERT:
        scanexp(t->check_assert);
        return;
    case CHECK_ERROR:
        scanexp(t->check_error);
        return;
    }
    assert(0);
}

static void set_invalid(Value *space, const int size) {
    for (int i = 0; i < size; i++) {
        space[i] = mkInvalid("invalid");
    }
}

/// Allocate space for the heap initially.
static void init_heap() {
    // calculate how much space we need
    int gamma = gammadesired(8, 2);
    int space = 3 * gamma;
    space /= 2;
    if (space % 2 == 1) {
        space ++;
    }
    // divide space into from-space and to-space
    semispacesize = space;
    fromspace = calloc(semispacesize, sizeof(Value));
    tospace = calloc(semispacesize, sizeof(Value));
    set_invalid(fromspace, semispacesize);
    set_invalid(tospace, semispacesize);
    hp = fromspace;
}

/// Move data from heap into a new, larger heap.
static void resize_heap(const long live_data) {
    // right after collecting & copying in to-space
    const int gamma = gammadesired(8, 2);
    long space = gamma * live_data;
    if (space % 2 == 1) {
        space ++;
    }
    space /= 2;
    printf("HEAP RESIZED from %d to %ld\n", semispacesize * 2, space * 2);

    int new_size = (int)space;
    {
        // increase spaces and account for potentially moving
        // pointers of realloc
        void * new_tospace = realloc(fromspace, new_size * sizeof(Value));
        fromspace = tospace;
        tospace = new_tospace;
        set_invalid(tospace, new_size);
        copy(); // moves all our pointers into the new, bigger space
        // fromspace is now garbage
        fromspace = realloc(fromspace, new_size * sizeof(Value));
        set_invalid(fromspace, new_size);
        hp = tospace + live_data;
        heaplimit = tospace + new_size;
    }
    if (!fromspace || !tospace) {
        printf("ERROR: couldn't allocate space for fromspace or tospace\n");
        exit(-1);
    }
    semispacesize = new_size;
}

/// Copy all live data in fromspace to tospace.
static void copy(void) {
    if (fromspace == NULL || tospace == NULL || semispacesize == 0) {
        init_heap();
    }

    hp = tospace;
    heaplimit = tospace + semispacesize;
    set_invalid(tospace, semispacesize);

    // loop through and scan root struct
    // 1) global vars
    scanenv(*roots.globals.user);

    const UnitTestlistlist ull = roots.globals.internal.pending_tests;
    const unsigned num_test_groups = lengthULL(ull);
    for (unsigned i = 0; i < num_test_groups; i++) {
        scantests(nthULL(ull, i));
    }

    // 2) stack
    // printf("copying stack\n");
    Frame *sp = roots.stack->frames;
    while (sp < roots.stack->sp) { // sp is the first unused frame
        scanframe(sp);
        sp ++;
    }

    // 3) registers
    // printf("copying registers\n");
    Registerlist reg = roots.registers;
    while (reg != NULL) {
        scanloc(reg->hd);
        reg = reg->tl;
    }

    // forward all the pointers in to-space
    Value *scanp = tospace;
    for (; scanp < hp; scanp++) {
        scanloc(scanp);
    }

    const long H = semispacesize * 2;
    const long L = hp - tospace;
    total_objects_copied += L;
    printf("Heap size: %ld; Live data size: %ld; H/L ratio: %f\n", H, L, (double)H/L);
}

/// Do a copy-collection.
static void collect(void) {
    // 1. forward roots
    copy();

    // 2. after we collect, if the heap is STILL full, we resize it
    long live_data = hp - tospace;
    if (live_data >= semispacesize - 1) {
        resize_heap(live_data);
    }

    // 3. swap from and to space
    Value *x = tospace;
    tospace = fromspace;
    fromspace = x;

    // 4. Get ready for next "mark" phase and collect metrics
    heaplimit = fromspace + semispacesize;
    if (num_collections % 10 == 0) {
        int H = semispacesize * 2;
        printf("Heap size: %d; Cells allocated: %d\n", H, nalloc);
    }
    num_collections ++;
}

/// Print final statistics.
void printfinalstats(void) {
    int H = semispacesize * 2;
    printf("Heap size: %d; Cells allocated: %d\n", H, nalloc);
    printf("Total collections: %d; Total objects copied: %d\n", num_collections, total_objects_copied);
}
/* you need to initialize this variable */
bool gc_uses_mark_bits = false;
