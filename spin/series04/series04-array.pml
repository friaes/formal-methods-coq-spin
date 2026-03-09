mtype = { farmer, wolf, sheep, cabbage };

// 0 = left, 1 = right
byte pos[4] = 0;

#define FARMER pos[farmer-1]
#define WOLF    pos[wolf-1]
#define SHEEP   pos[sheep-1]
#define CABBAGE pos[cabbage-1]

#define FINAL !(FARMER == 1 && WOLF == 1 && SHEEP == 1 && CABBAGE == 1)

inline valid_state() {
    ((FARMER == WOLF || WOLF != SHEEP) && // farmer cant leave wolf with sheep alone
     (FARMER == SHEEP || SHEEP != CABBAGE)) // farmer cant leave sheep with cabbage alone
}

active proctype RiverCrossing() {
    do
    ::  // Farmer crosses alone
        FARMER = 1 - FARMER;
        printf("Farmer crosses alone\n");
        valid_state();
        assert(FINAL);

    ::  // Farmer crosses with wolf
        FARMER == WOLF;
        FARMER = 1 - FARMER;
        WOLF = 1 - WOLF;
        printf("Farmer crosses with wolf\n");
        valid_state();
        assert(FINAL);

    ::  // Farmer crosses with sheep
        FARMER == SHEEP;
        FARMER = 1 - FARMER;
        SHEEP = 1 - SHEEP;
        printf("Farmer crosses with sheep\n");
        valid_state();
        assert(FINAL);

    ::  // Farmer crosses with cabbage
        FARMER == CABBAGE;
        FARMER = 1 - FARMER;
        CABBAGE = 1 - CABBAGE;
        printf("Farmer crosses with cabbage\n");
        valid_state();
        assert(FINAL);
    od
}
