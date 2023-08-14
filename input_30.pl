edge(0, 1).
edge(1, 2).
edge(2, 3).
edge(3, 4).
edge(4, 5).
edge(5, 0).
edge(5, 6).
edge(6, 7).
edge(7, 8).
edge(8, 9).
edge(9, 10).
edge(10, 11).
edge(11, 12).
edge(12, 13).
edge(13, 14).
edge(14, 15).
edge(15, 16).
edge(16, 17).
edge(17, 18).
edge(18, 19).
edge(19, 20).
edge(20, 21).
edge(21, 22).
edge(22, 23).
edge(23, 24).
edge(24, 25).
edge(25, 26).
edge(26, 27).
edge(27, 28).
edge(28, 29).
edge(29, 30).
edge(30, 0).

reachable(X,Y) :- edge(X,Y).
reachable(X,Y) :- edge(X,Z), reachable(Z,Y).
same_clique(X,Y) :- reachable(X,Y), reachable(Y,X).