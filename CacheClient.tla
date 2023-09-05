------ MODULE CacheClient ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Proc

VARIABLES pc, local_cmd, local_send, recv_pc, send_buf, recv_buf, next_req,
    conn_set, recv_current

Cmd == [ req: Nat, resp: Nat, finished: BOOLEAN ]

Conn == [ write: Seq(Nat), read: Seq(Nat),
    server_closed: BOOLEAN, client_closed: BOOLEAN ]

recv_vars == <<recv_pc, recv_buf, recv_current>>

ProcState == {"Init", "ReadSendBuf", "PushToRecvBuf", 
    "WriteToConn", "WaitResponse", "Terminated"}

current_conn == conn_set[Len(conn_set)]

update_current_conn(c) ==
    conn_set' = [conn_set EXCEPT ![Len(conn_set)] = c]

write_to_current(req) ==
    update_current_conn([current_conn EXCEPT !.write = Append(@, req)])

read_from_current == current_conn.read[1]


TypeOK ==
    /\ pc \in [Proc -> ProcState]
    /\ local_cmd \in [Proc -> Cmd]
    /\ recv_pc \in {"Init", "RecvReadConn"}
    /\ recv_buf \in Seq(Proc)
    /\ send_buf \in Seq(Proc)
    /\ next_req \in Nat
    /\ local_send \in [Proc -> Seq(Proc)]
    /\ conn_set \in Seq(Conn)
    /\ recv_current \in Proc \union {"none"}


newReq(r) == [req |-> r, resp |-> 0, finished |-> FALSE ]


newConn ==
    [ write |-> <<>>, read |-> <<>>,
    server_closed |-> FALSE, 
    client_closed |-> FALSE ]


Init ==
    /\ pc = [p \in Proc |-> "Init"]
    /\ local_cmd = [p \in Proc |-> newReq(0)]
    /\ recv_pc = "Init"
    /\ recv_buf = <<>>
    /\ send_buf = <<>>
    /\ next_req = 11
    /\ local_send = [p \in Proc |-> <<>>]
    /\ conn_set = <<newConn>>
    /\ recv_current = "none"


goto(p, l) ==
    pc' = [pc EXCEPT ![p] = l]


PushCmd(p) ==
    /\ pc[p] = "Init"
    /\ Len(send_buf) < 2
    /\ local_cmd' = [local_cmd EXCEPT ![p] = newReq(next_req)]
    /\ send_buf' = Append(send_buf, p)
    /\ IF Len(send_buf) = 0
        THEN goto(p, "ReadSendBuf")
        ELSE goto(p, "WaitResponse")
    /\ next_req' = next_req + 1
    /\ UNCHANGED recv_vars
    /\ UNCHANGED local_send
    /\ UNCHANGED conn_set


ReadSendBuf(p) ==
    /\ pc[p] = "ReadSendBuf"
    /\ goto(p, "PushToRecvBuf")
    /\ local_send' = [local_send EXCEPT ![p] = send_buf]
    /\ send_buf' = <<>>
    /\ UNCHANGED next_req
    /\ UNCHANGED recv_vars
    /\ UNCHANGED conn_set
    /\ UNCHANGED local_cmd


PushToRecvBuf(p) ==
    /\ pc[p] = "PushToRecvBuf"
    /\ Len(recv_buf) < 2
    /\ recv_buf' = Append(recv_buf, local_send[p][1])
    /\ goto(p, "WriteToConn")
    /\ UNCHANGED local_send
    /\ UNCHANGED next_req
    /\ UNCHANGED send_buf
    /\ UNCHANGED <<recv_pc, recv_current>>
    /\ UNCHANGED conn_set
    /\ UNCHANGED local_cmd


getCmd(p) == local_cmd[p]


WriteToConn(p) ==
    /\ pc[p] = "WriteToConn"
    /\ write_to_current(getCmd(local_send[p][1]).req)
    /\ local_send' = [local_send EXCEPT ![p] = Tail(local_send[p])]
    /\ IF Len(local_send'[p]) = 0
        THEN goto(p, "WaitResponse")
        ELSE goto(p, "PushToRecvBuf")
    /\ UNCHANGED next_req
    /\ UNCHANGED recv_vars
    /\ UNCHANGED send_buf
    /\ UNCHANGED local_cmd


RecvGetNextCmd ==
    /\ recv_pc = "Init"
    /\ recv_pc' = "RecvReadConn"
    /\ Len(recv_buf) > 0
    /\ recv_current' = recv_buf[1]
    /\ recv_buf' = Tail(recv_buf)
    /\ UNCHANGED <<pc, local_cmd, local_send>>
    /\ UNCHANGED next_req
    /\ UNCHANGED conn_set
    /\ UNCHANGED send_buf


update_cmd_resp(cmd, r) ==
    [cmd EXCEPT !.resp = r, !.finished = TRUE ]

consume_conn_write(c, r) ==
    [c EXCEPT !.write = Tail(@), !.read = Append(@, r + 10) ]


MemcachedResponse(i) ==
    /\ conn_set[i].server_closed = FALSE
    /\ Len(conn_set[i].write) > 0
    /\ LET e == conn_set[i].write[1] IN
        conn_set' = [conn_set EXCEPT ![i] = consume_conn_write(@, e)]
    /\ UNCHANGED <<pc, local_cmd, local_send>>
    /\ UNCHANGED recv_vars
    /\ UNCHANGED next_req
    /\ UNCHANGED send_buf


RecvReadConn ==
    /\ recv_pc = "RecvReadConn"
    /\ Len(current_conn.read) > 0
    /\ recv_pc' = "Init"
    /\ LET r == read_from_current IN
        /\ local_cmd' = [local_cmd EXCEPT ![recv_current] = update_cmd_resp(@, r)]
        /\ update_current_conn([current_conn EXCEPT !.read = Tail(@)])
    /\ UNCHANGED <<pc, local_send>>
    /\ UNCHANGED send_buf
    /\ UNCHANGED recv_current
    /\ UNCHANGED next_req
    /\ UNCHANGED recv_buf


Terminated ==
    /\ \A p \in Proc: pc[p] = "Terminated"
    /\ recv_pc = "Terminated"

Next ==
    \/ \E p \in Proc:
        \/ PushCmd(p)
        \/ ReadSendBuf(p)
        \/ PushToRecvBuf(p)
        \/ WriteToConn(p)
    \/ RecvGetNextCmd
    \/ RecvReadConn
    \/ \E i \in DOMAIN conn_set: MemcachedResponse(i)
    \/ Terminated

Perms == Permutations(Proc)

====