byte var = 0;

active proctype A(){
    start:
        var++;
        goto start
}

never {
    do
    :: (var == 255) -> break;
    :: else;
    od
}

