------ MODULE CacheClient ----
EXTENDS TLC, Sequences, Naturals

CONSTANTS Proc

VARIABLES pc, local_cmd, local_send, recv_pc, send_buf,
    recv_buf, recv_buf_closed, next_req,
    conn_set, recv_current, conn_locked,
    write_cmd_count, recv_cmd_count

Cmd == [ req: Nat, resp: Nat, finished: BOOLEAN, conn: Nat]

Conn == [ write: Seq(Nat), read: Seq(Nat),
    server_closed: BOOLEAN, client_closed: BOOLEAN ]

local_vars == <<pc, local_cmd, local_send>>

recv_vars == <<recv_pc, recv_buf, recv_buf_closed, recv_current, recv_cmd_count>>

ProcState == {"Init", "ReadSendBuf", "PushToRecvBuf", 
    "WriteToConn", "WaitResponse", "Terminated"}

current_conn == conn_set[Len(conn_set)]

current_conn_index == Len(conn_set)

update_current_conn(c) ==
    conn_set' = [conn_set EXCEPT ![Len(conn_set)] = c]

send_buf_limit == 3
conn_write_limit == 3
recv_buf_limit == 3


write_to_current_err(req) ==
    /\ \/ current_conn.client_closed = TRUE
       \/ current_conn.server_closed = TRUE
    /\ UNCHANGED conn_set


write_to_current_success(req) ==
    /\ current_conn.client_closed = FALSE
    /\ current_conn.server_closed = FALSE
    /\ Len(current_conn.write) < conn_write_limit
    /\ update_current_conn([current_conn EXCEPT !.write = Append(@, req)])


write_to_current(req) ==
    \/ write_to_current_success(req)
    \/ write_to_current_err(req)


TypeOK ==
    /\ pc \in [Proc -> ProcState]
    /\ local_cmd \in [Proc -> Cmd]
    /\ recv_pc \in {"Init", "RecvReadConn", "RecvDoCloseConn", "Terminated"}
    /\ recv_buf \in Seq(Proc)
    /\ send_buf \in Seq(Proc)
    /\ next_req \in Nat
    /\ local_send \in [Proc -> Seq(Proc)]
    /\ conn_set \in Seq(Conn)
    /\ recv_current \in Proc \union {"none"}
    /\ recv_buf_closed \in BOOLEAN
    /\ conn_locked \in BOOLEAN
    /\ write_cmd_count \in Nat
    /\ recv_cmd_count \in Nat


newReq(r) == [req |-> r, resp |-> 0, finished |-> FALSE, conn |-> 0]


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
    /\ recv_buf_closed = FALSE
    /\ conn_locked = FALSE
    /\ write_cmd_count = 0
    /\ recv_cmd_count = 0


goto(p, l) ==
    pc' = [pc EXCEPT ![p] = l]


PushCmd(p) ==
    /\ pc[p] = "Init"
    /\ Len(send_buf) < send_buf_limit
    /\ local_cmd' = [local_cmd EXCEPT ![p] = newReq(next_req)]
    /\ send_buf' = Append(send_buf, p)
    /\ IF Len(send_buf) = 0
        THEN goto(p, "ReadSendBuf")
        ELSE goto(p, "WaitResponse")
    /\ next_req' = next_req + 1
    /\ UNCHANGED recv_vars
    /\ UNCHANGED local_send
    /\ UNCHANGED conn_set
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


ReadSendBuf(p) ==
    /\ pc[p] = "ReadSendBuf"
    /\ conn_locked = FALSE
    /\ conn_locked' = TRUE
    /\ goto(p, "PushToRecvBuf")
    /\ local_send' = [local_send EXCEPT ![p] = send_buf]
    /\ send_buf' = <<>>
    /\ UNCHANGED next_req
    /\ UNCHANGED recv_vars
    /\ UNCHANGED conn_set
    /\ UNCHANGED local_cmd
    /\ UNCHANGED write_cmd_count


removeLocalSend(p) ==
    /\ local_send' = [local_send EXCEPT ![p] = Tail(local_send[p])]
    /\ IF Len(local_send'[p]) = 0
        THEN
            /\ goto(p, "WaitResponse")
            /\ conn_locked' = FALSE
        ELSE
            /\ goto(p, "PushToRecvBuf")
            /\ UNCHANGED conn_locked


update_cmd_resp(cmd, r) ==
    [cmd EXCEPT !.resp = r, !.finished = TRUE ]


allowWriteLimit == 2

allowToWrite ==
    /\ write_cmd_count < recv_cmd_count + allowWriteLimit
    /\ write_cmd_count' = write_cmd_count + 1


pushToRecvBufNormal(p) ==
    LET cmd_ptr == local_send[p][1] IN
        /\ recv_buf_closed = FALSE
        /\ local_cmd' = [local_cmd EXCEPT ![cmd_ptr] = [@ EXCEPT !.conn = current_conn_index]]
        /\ Len(recv_buf) < recv_buf_limit
        /\ allowToWrite
        /\ recv_buf' = Append(recv_buf, cmd_ptr)
        /\ goto(p, "WriteToConn")
        /\ UNCHANGED local_send
        /\ UNCHANGED conn_locked

pushToRecvBufClosed(p) ==
    /\ recv_buf_closed = TRUE
    /\ local_cmd' = [local_cmd EXCEPT ![local_send[p][1]] = update_cmd_resp(@, 0)]
    /\ removeLocalSend(p)
    /\ UNCHANGED write_cmd_count
    /\ UNCHANGED recv_buf

PushToRecvBuf(p) ==
    /\ pc[p] = "PushToRecvBuf"
    /\ \/ pushToRecvBufNormal(p)
       \/ pushToRecvBufClosed(p)
    /\ UNCHANGED next_req
    /\ UNCHANGED send_buf
    /\ UNCHANGED <<recv_pc, recv_current, recv_cmd_count>>
    /\ UNCHANGED conn_set
    /\ UNCHANGED recv_buf_closed


getCmd(p) == local_cmd[p]

WriteToConn(p) ==
    /\ pc[p] = "WriteToConn"
    /\ write_to_current(getCmd(local_send[p][1]).req)
    /\ removeLocalSend(p)
    /\ UNCHANGED next_req
    /\ UNCHANGED recv_vars
    /\ UNCHANGED send_buf
    /\ UNCHANGED local_cmd
    /\ UNCHANGED write_cmd_count

WaitResponse(p) ==
    /\ pc[p] = "WaitResponse"
    /\ local_cmd[p].finished = TRUE
    /\ goto(p, "Terminated")
    /\ UNCHANGED recv_vars
    /\ UNCHANGED <<send_buf, next_req>>
    /\ UNCHANGED local_cmd
    /\ UNCHANGED conn_set
    /\ UNCHANGED conn_locked
    /\ UNCHANGED local_send
    /\ UNCHANGED write_cmd_count


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
    /\ UNCHANGED <<recv_buf_closed, recv_cmd_count>>
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count

RecvDoTerminate ==
    /\ recv_pc = "Init"
    /\ Len(recv_buf) = 0
    /\ recv_buf_closed = TRUE
    /\ update_current_conn([current_conn EXCEPT !.client_closed = TRUE, !.server_closed = TRUE])
    /\ recv_pc' = "Terminated"
    /\ UNCHANGED <<pc, local_cmd, local_send>>
    /\ UNCHANGED send_buf
    /\ UNCHANGED next_req
    /\ UNCHANGED <<recv_buf, recv_current, recv_buf_closed, recv_cmd_count>>
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


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
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


MemcachedCloseConn(i) ==
    /\ conn_set[i].server_closed = FALSE
    /\ conn_set' = [conn_set EXCEPT ![i] = [@ EXCEPT !.server_closed = TRUE]]
    /\ UNCHANGED local_vars
    /\ UNCHANGED next_req
    /\ UNCHANGED send_buf
    /\ UNCHANGED recv_vars
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


MemcachedResetNewConn ==
    /\ conn_locked = FALSE
    /\ recv_buf_closed = FALSE
    /\ current_conn.client_closed = TRUE
    /\ conn_set' = Append(conn_set, newConn)
    /\ UNCHANGED local_vars
    /\ UNCHANGED recv_vars
    /\ UNCHANGED send_buf
    /\ UNCHANGED next_req
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


recvConn == conn_set[local_cmd[recv_current].conn]

updateRecvConn(c) ==
    conn_set' = [conn_set EXCEPT ![local_cmd[recv_current].conn] = c]

recvReadFromCurrent == recvConn.read[1]

recvReadConnNormal ==
    /\ Len(recvConn.read) > 0
    /\ recv_pc' = "Init"
    /\ LET r == recvReadFromCurrent IN
        /\ local_cmd' = [local_cmd EXCEPT ![recv_current] = update_cmd_resp(@, r)]
        /\ updateRecvConn([recvConn EXCEPT !.read = Tail(@)])


recvReadConnServerClosed ==
    /\ recvConn.server_closed = TRUE
    /\ recv_pc' = "RecvDoCloseConn"
    /\ local_cmd' = [local_cmd EXCEPT ![recv_current] = update_cmd_resp(@, 0)]
    /\ UNCHANGED conn_set


RecvReadConn ==
    /\ recv_pc = "RecvReadConn"
    /\ \/ recvReadConnNormal
       \/ recvReadConnServerClosed 
    /\ recv_cmd_count' = recv_cmd_count + 1
    /\ UNCHANGED <<pc, local_send>>
    /\ UNCHANGED send_buf
    /\ UNCHANGED recv_current
    /\ UNCHANGED next_req
    /\ UNCHANGED recv_buf
    /\ UNCHANGED recv_buf_closed
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count

RecvDoCloseConn ==
    /\ recv_pc = "RecvDoCloseConn"
    /\ recv_pc' = "Init"
    /\ updateRecvConn([recvConn EXCEPT !.client_closed = TRUE])
    /\ UNCHANGED local_vars
    /\ UNCHANGED <<recv_buf, recv_buf_closed, recv_current, recv_cmd_count>>
    /\ UNCHANGED <<send_buf, next_req>>
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


DoCloseRecv ==
    /\ recv_buf_closed = FALSE
    /\ recv_buf_closed' = TRUE
    /\ UNCHANGED <<pc, local_cmd, local_send>>
    /\ UNCHANGED conn_set
    /\ UNCHANGED next_req
    /\ UNCHANGED <<recv_buf, recv_current, recv_pc, send_buf, recv_cmd_count>>
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


Terminated ==
    /\ \A p \in Proc: pc[p] = "Terminated"
    /\ recv_pc = "Terminated"
    /\ UNCHANGED <<pc, local_cmd, local_send>>
    /\ UNCHANGED <<conn_set, next_req>>
    /\ UNCHANGED recv_vars
    /\ UNCHANGED send_buf
    /\ UNCHANGED conn_locked
    /\ UNCHANGED write_cmd_count


Next ==
    \/ \E p \in Proc:
        \/ PushCmd(p)
        \/ ReadSendBuf(p)
        \/ PushToRecvBuf(p)
        \/ WriteToConn(p)
        \/ WaitResponse(p)
    \/ \E i \in DOMAIN conn_set:
        \/ MemcachedResponse(i)
        \/ MemcachedCloseConn(i)
    \/ RecvGetNextCmd
    \/ RecvReadConn
    \/ DoCloseRecv
    \/ RecvDoTerminate
    \/ RecvDoCloseConn
    \/ MemcachedResetNewConn
    \/ Terminated

FinishWithClosed ==
    (
        /\ \A p \in Proc: pc[p] = "Terminated"
        /\ recv_pc = "Terminated"
    ) => (\A i \in DOMAIN conn_set:
            /\ conn_set[i].client_closed = TRUE
            /\ conn_set[i].server_closed = TRUE
            /\ write_cmd_count = recv_cmd_count
         )


CloseOnlyOnServerClosed ==
    recv_pc = "RecvDoCloseConn" => (
        /\ recv_current /= "none"
        /\ recvConn.server_closed = TRUE
    )

RespectWriteLimit ==
    Len(current_conn.write) <= allowWriteLimit


Perms == Permutations(Proc)

====
