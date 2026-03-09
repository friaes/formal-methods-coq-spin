## Exercise 2.1
A) No, Spin wont detect an error, because with weak fairness contraint, if a process is continuously enabled, then it must eventually make progress, and in this model, both A and B are always enabled because x = 3 - x is always a valid operation.
B) No, Spin wont detect an error, because both processes can eventually execute their progress: statements, so Spin cannot find a non-progress cycle.
## Exercise 2.2
With a progress label in only process A, Spin will detect a non progress cycle without weak fairness constraint, because it’s possible for B to run forever, and A to be starved, even though it's enabled. If A never gets scheduled, the progress: label is never reached, which constitutes a non-progress cycle.