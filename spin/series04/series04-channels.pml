mtype = { farmer, wolf, sheep, cabbage };
chan left  = [4] of { mtype };
chan right = [4] of { mtype };

#define FINAL (right??[farmer] && right??[wolf] && right??[sheep] && right??[cabbage])

inline move(from, to, who1, who2) {
    from??who1;
    from??who2;
    printf("Crossing: %e %e\n", who1, who2);
    to!!who1;
    to!!who2;
    assert(!FINAL);
}

inline move_alone(from, to, who) {
    from??who;
    printf("Crossing: %e\n", who);
    to!!who;
    assert(!FINAL);
}

inline safe() {
    // Block execution if wolf and sheep are alone without farmer
    !( (left??[wolf] && left??[sheep] && !left??[farmer]) ||
       (right??[wolf] && right??[sheep] && !right??[farmer]) ||

    // Block execution if sheep and cabbage are alone without farmer
       (left??[sheep] && left??[cabbage] && !left??[farmer]) ||
       (right??[sheep] && right??[cabbage] && !right??[farmer]) )
}


active proctype river() {
    // Initialize everything on left shore
    left!!farmer; left!!wolf; left!!sheep; left!!cabbage;

    do
    // Farmer crosses alone to the right shore
    :: left??[farmer] ->
        move_alone(left, right, farmer); safe();
    // Farmer crosses with the wolf to the right shore
    :: left??[farmer] && left??[wolf] ->
        move(left, right, farmer, wolf); safe();
    
    :: left??[farmer] && left??[sheep] ->
        move(left, right, farmer, sheep); safe();

    :: left??[farmer] && left??[cabbage] ->
        move(left, right, farmer, cabbage); safe();

    :: right??[farmer] ->
        move_alone(right, left, farmer); safe();

    :: right??[farmer] && right??[wolf] ->
        move(right, left, farmer, wolf); safe();

    :: right??[farmer] && right??[sheep] ->
        move(right, left, farmer, sheep); safe();

    :: right??[farmer] && right??[cabbage] ->
        move(right, left, farmer, cabbage); safe();
    od

}
