#include "all.h"
/* copy.c ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) */
/* private declarations for copying collection 276a */
static Value *fromspace, *tospace; // used only at GC time
static int semispacesize;          // # of objects in fromspace or tospace
/* private declarations for copying collection 276b */
static Value *hp, *heaplimit;      // used for every allocation
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
    if (hp == heaplimit)
        collect();
    assert(hp < heaplimit);
    assert(isinspace(hp, fromspace)); /*runs after spaces are swapped*/ /*OMIT*/
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

static void resize_heap(const long live_data) {
    // right after collecting & copying in to-space
    const int gamma = gammadesired(8, 2);
    long space = gamma * live_data;
    space /= 2;
    if (space % 2 == 1) {
        space ++;
    }
    printf("HEAP RESIZED from semispace size %d to %ld\n", semispacesize, space);

    int new_size = (int)space;
    {
        // increase spaces and account for potentially moving
        // pointers of realloc
        void * new_tospace = realloc(fromspace, new_size * sizeof(Value));
        fromspace = tospace;
        tospace = new_tospace;
        copy(); // moves all our pointers into the new, bigger space
        // fromspace is now garbage
        fromspace = realloc(fromspace, new_size * sizeof(Value));
    }
    // set them to be invalid
    set_invalid(fromspace, new_size);
    set_invalid(tospace + semispacesize, new_size - semispacesize);
    semispacesize = new_size;
    if (!fromspace || !tospace) {
        printf("ERROR: couldn't allocate space for fromspace or tospace\n");
        exit(-1);
    }
    if (isinspace(heaplimit, fromspace)) {
        heaplimit = fromspace + semispacesize - 1;
    } else if (isinspace(heaplimit, tospace)) {
        heaplimit = tospace + semispacesize - 1;
    } else {
        printf("ERROR: heaplimit is not in the heap 💀💀💀\n");
    }
}

static void copy(void) {
    if (fromspace == NULL || tospace == NULL || semispacesize == 0) {
        init_heap();
    }

    hp = tospace;
    heaplimit = tospace + semispacesize - 1;

    // loop through and scan root struct
    // 1) global vars
    scanenv(*roots.globals.user);
    const UnitTestlistlist ull = roots.globals.internal.pending_tests;
    const unsigned num_test_groups = lengthULL(ull);
    for (unsigned i = 0; i < num_test_groups; i++) {
        scantests(nthULL(ull, i));
    }

    // 2) stack
    Frame *sp = roots.stack->frames;
    while (sp <= roots.stack->sp) {
        scanframe(sp);
        sp ++;
    }

    // 3) registers
    Registerlist reg = roots.registers;
    while (reg != NULL) {
        scanloc(reg->hd);
        reg = reg->tl;
    }
}

/* you need to redefine these functions */
static void collect(void) {
    // 1. forward roots
    copy();

    // 2. forward everything in to-space (updating the pointers)?


    // 3. after we collect, if the heap is STILL full, we resize it
    long live_data = hp - tospace;
    if (isinspace(hp, tospace)) {
        printf("hp is in tospace\n");
    } else if (isinspace(hp, fromspace)) {
        printf("hp is in fromspace\n");
    }
    printf("hp: %p, live data size: %ld\n", (void*)hp, live_data);
    if (live_data == semispacesize) {
        resize_heap(live_data);
    }

    // 4. swap from and to space
    Value *x = tospace;
    tospace = fromspace;
    fromspace = x;

    heaplimit = fromspace + semispacesize - 1;
}
void printfinalstats(void) { assert(0); }
/* you need to initialize this variable */
bool gc_uses_mark_bits = false;
