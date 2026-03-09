byte var = 0;

active proctype process1() {
    start:
        if
        :: var < 255 -> var++;
        :: else 
        fi
        goto start
}

active proctype process2() {
    start:
        if
        :: var > 0 -> var--;
        :: else;
        fi
        goto start
}

never {
    do
    :: var == 255 -> break;
    :: else;
    od
}
