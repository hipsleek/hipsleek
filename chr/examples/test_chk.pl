guard(hb(event(X,1),event(Z,3))),cb(event(X,1),event(Y,1)),hb(event(X,0),event(Y,1)),hb(event(Y,1),event(Z,3)),hb(event(Y,4),event(Z,5)).


%cb(event(X,1),event(Y,1)),hb(event(Y,1),event(Z,3)),hb(event(Y,4),event(Z,5)),guard(hb(event(X,1),event(Z,3))).
%hb(event(X,1),event(Y,2)),hb(event(Y,2),event(Z,3)),hb(event(Y,4),event(Z,5)),guard(hb(event(X,1),event(Z,3))).
%hb(event(X,1),event(Y,2)),hb(event(Y,2),event(Z,3)),guard(hb(event(X,1),event(Z,3))).
%imp(and(hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3))),hb(event(X,1),event(Z,3))).
% and(hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3))).
%imp(and(hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3))),hb(event(X,1),event(Z,3))).
%imp(hb(event(X,1),event(Z,3)),hb(event(X,1),event(Z,5))).
% hb(event(X,1),event(Y,2)), hb(event(Y,2),event(Z,3)), hb(event(Z,3),event(T,a)), hb(event(Z,5),event(T,b)). 