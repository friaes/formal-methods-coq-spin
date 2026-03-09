## Exercise 2.1 & 2.2
Regardless of which init command we use, the never claim can still
be violated. This is because both init commands only determine how
the processes are started, not how they execute. In the first init 
command, process1 is started before process2, while in the second, 
both processes are started simultaneously. However, in both cases,
the execution of the processes is still subject to interleaving. 
This means that process2 can run multiple times before process1 gets
a chance to execute, leading to a situation where "b" becomes 
greater than "a", and thus the condition "a < b" becomes true, 
violating the never claim.

## Exercise 2.3
In this case the never claim cannot be violated. This is because
both operations (a = a*2 and b = b+2) are now executed sequentially
within the same process, ensuring "a" always grows faster than "b".