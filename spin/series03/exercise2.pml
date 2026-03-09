byte x = 2;
bool flagA = false;
bool flagB = false;

active proctype A() {
    do
    :: x = 3 - x;
        flagA = true;
    od
}

active proctype B() {
    do
    :: x = 3 - x;
        flagB = true;
    od
}

active proctype Monitor() {
    do
    :: (flagA);
        progress: skip;
        flagA = false
    :: (flagB);
        progress: skip;
        flagB = false
    od
}
