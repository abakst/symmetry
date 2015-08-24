data Message = Ping ProcessId
             | Pong ProcessId
  deriving (Typeable, Generic)


instance Binary Message


-- simple eg of receive a ping and then reply with a pong
-- \ex x : T .{ v: Process () |  { stmt v = sseq ((srecv (Ping x)) (ssend x Message))}  where T = ?}
f1 = do 
       Ping from <- expect
       mypid <- getSelfPid
       send from (Pong mypid)


-- \ex x1 : T1, x2 : T2 .  { v: Process () |  {stmt v = sseq ((srecv (Ping x1)) (
--                                                      sseq (srecv (Ping x2)) 
--														     (ssend x1 (Pong x2)) ))} where T1, T2 = ?}
f2 = do
	   Ping id1 <- expect
	   Ping id2 <- expect
	   send id1 (Pong id2)









