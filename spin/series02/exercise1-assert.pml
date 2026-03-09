byte var = 0;

active proctype A(){
    start:
        var++;
        assert(var != 255);
        goto start
}