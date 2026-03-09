## Exercise 1
### 1. <>p /\ q <-> <>(p /\ q) is not valid.
- this equivalence is not valid, because <>p /\ q means that q holds at the initial state and p eventually holds somewhere in the future, whereas <>(p /\ q) means that p and q are both true eventually in the future.

### 2. []p /\ []q <-> [](p /\ q) is valid.
- []p /\ []q -> [](p /\ q) If p is always true and q is always true, then p /\ q must also be always true.
- []p /\ []q <- [](p /\ q) If p /\ q is always true, then both p and q must individually be always true.

### 3. <>(q U p) <-> <>q is not valid.
- this equivalence is not valid, because <>(q U p) means that q must be true until p becomes true, and p must eventually occur. So, q may repeatedly hold (or not at all since U allows q to be vacuously true if p is true now), thus <>(q U p) <-> <>p being the actual valid ltl equivalence.

## Exercise 2
### 1. 
```bash
never  {
        do
        :: (1) -> skip
        :: (q) -> goto accept
        od
accept:
        do
        :: (q) -> goto accept
        od
}
```

### 2. 
```bash
never  {    /* <>[]q */
T0_init:
        do
        :: ((q)) -> goto accept_S4
        :: (1) -> goto T0_init
        od;
accept_S4:
        do
        :: ((q)) -> goto accept_S4
        od;
}
```

## Exercise 3
- XXp
- !p /\ X!p /\ XXp
- []q /\ []<>p
- <>(q /\ X[]p)
- []!(q /\ p)