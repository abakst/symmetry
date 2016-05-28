===========
Loop free:
===========

"Single ping":
--------------
P1=seq([send(e_pid(m),e_pid(p),m), recv(m, x1)]),
P2=seq([recv(p, id), send(e_pid(p),e_var(id),p)]),
T=(par([P1,P2])),
rewrite(T, _, Delta1, Rho1).

"Send first":
-------------
P1=seq([send(e_pid(p0),e_pid(p1),p0),recv(p0,x1)]),
P2=seq([send(e_pid(p1), e_pid(p0), p1), recv(p1,x1)]),
T=(par([P1,P2])),
rewrite(T, _, Delta1, Rho1).

"Registry":
-----------
M=seq([send(e_pid(m),e_pid(p1),r),send(e_pid(m),e_pid(p2),r),recv(m,x1),send(e_pid(m),e_pid(r),m)]), R=seq([recv(r, x1),recv(r, x2),send(e_pid(r),e_pid(m),a),recv(r, x3)]),
P1=seq([recv(p1, x1),send(e_pid(p1),e_var(x1),p1)]),
P2=seq([recv(p2, x1),send(e_pid(p2),e_var(x1),p2)]),
T= par([M,R,P1,P2]),
rewrite(T, _, Delta1, Rho1).

===========
  Loops:
===========
% Simple ping
P1=seq([send(e_pid(m),e_pid(Q),m),recv(m,x)]),
P2=seq([recv(P, id),send(e_pid(P),e_pid(m),P)]),
T=(par([for(Q, s, P1), sym(P, s, P2)])),
rewrite(T, _, Delta1, Rho1).

% Reverse ping
P1=seq([recv(m,id), send(e_pid(m),e_var(id),m)]),
P2=seq([send(e_pid(P),e_pid(m),P), recv(P, x)]),
T=(par([for(Q, s, P1), sym(P, s, P2)])),
rewrite(T, _, Delta1, Rho1).

% Two loops
P1A=seq([send(e_pid(m),e_pid(Q),m)]),
P1B=seq([recv(m,x)]),
P2=seq([recv(P, id),send(e_pid(P),e_pid(m),P)]),
T=(par([seq([for(Q, s, P1A),for(Q, s, P1B)]), sym(P, s, P2)])),
rewrite(T, _, Delta1, Rho1).

% Reverse ping: two loops
P1A=seq([send(e_pid(m),e_pid(Q), m)]),
P1B=seq([recv(m, x)]),
P2=seq([recv(P, id), send(e_pid(P),e_var(id),P)]),
T=(par([for(Q, s, P1A), for(Q, s, P1B), sym(P, s, P2)])),
rewrite(T, _, Delta1, Rho1).

% Double ping: 
P1=seq([send(e_pid(m),e_pid(Q),m),send(e_pid(m),e_pid(Q),m),recv(m,id1),recv(m,id2)]),
P2=seq([send(e_pid(P),e_pid(m),P),send(e_pid(P),e_pid(m),P), recv(P, x1), recv(P, x2)]),
T=(par([for(Q, s, P1), sym(P, s, P2)])),
rewrite(T, _, Delta1, Rho1).