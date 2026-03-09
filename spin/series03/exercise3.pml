chan global = [0] of { bool };
byte counter0 = 0;
byte counter1 = 0;

active proctype sender() {
do
:: skip;
:: global!0;
:: global!1;
od ; 
}
active proctype receiver() {
do
:: skip;
:: global?0; counter0++;
:: global?1; counter1++;
od ; 
}