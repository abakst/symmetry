module Tests where
import AST
import Render

-- t0 = Config { cTypes = [ MTApp (MTyCon "PING") [PVar (V "x")]
--                   , MTApp (MTyCon "PONG") [PVar (V "x")]
--                   ]

--        , cSets  = []

--        , cProcs = [(PConc 0,
--                    [ Choose (V "pi") (S "ps")
--                        [Send (PVar (V "pi")) [(MTApp (MTyCon "PING") [PConc 0],
--                                                         [Recv [(MTApp (MTyCon "PONG") [PVar (V "x")], [])] ()])] ()] ()]),
--             (PAbs (V "p") (S "ps"),
--              [Loop (V "X")
--                       [Recv [(MTApp (MTyCon "PING") [PVar (V "x")],
--                               [Send (PVar (V "x")) [(MTApp (MTyCon "PONG") [PVar (V "x")], [Goto (V "X") ()])] ()])] ()] ()])]
-- }

-- ---

mPing, mPong :: Pid -> MType
mPing v = MTApp (MTyCon "Ping") [v]
mPong v = MTApp (MTyCon "Pong") [v]

tpid0, tpid1, tpid2 :: Pid
tpid0 = PConc 0
tpid1 = PConc 1
tpid2 = PAbs (V "p") (S "ps")

pvar :: String -> Pid
pvar x = PVar (V x)

test0 :: Config ()
test0 = Config {
          cTypes  = [mPing (pvar "x"),
                     mPong (pvar "x"),
                     MTApp (MTyCon "Unit") []]
        , cSets   = []
        , cUnfold = []
        , cProcs  = [
         (tpid0, Send tpid1 [(mPing tpid0, Recv [(mPong (pvar "x"), Skip ())] ())] ())
        ,(tpid1, Recv [(mPing (pvar "x"), Send (pvar "x") [(mPong tpid1, Skip ())] ())] ())
                    ]
        } :: Config ()

-- test0a = Config {
--   cTypes = [mPing (pvar "x"), mPong (pvar "x"), MTApp (MTyCon "Unit") []]
--   , cSets  = []
--   , cProcs = [(tpid0,
--                     [Loop (V "X")
--                       [Send tpid1 [(mPing tpid0, [Recv [(mPong (pvar "x"), [Goto (V "X") ()])] ()])] ()] ()])
--              ,(tpid1,
--                     [Loop (V "Y")
--                       [Recv [(mPing (pvar "x"), [Send (pvar "x") [(mPong tpid1, [Goto (V "Y") ()])] ()])] ()] ()])]
-- }

test1 :: Config ()
test1= Config {
         cTypes = [mPing (pvar "x"), mPong (pvar "x"), MTApp (MTyCon "Unit") []]
       , cSets  = []
       , cUnfold = []
  , cProcs = [(tpid0,
                Iter (V "pi") (S "ps")
                  (Block [Send (PVar (V "pi")) [(mPing tpid0, Recv [(mPong (pvar "x"), Skip ())] ())] ()] ()) ())
             ,(tpid2, Recv [(mPing (pvar "x"), Send (pvar "x") [(mPong tpid2, Skip ())] ())] ())]
}

test1unfold :: Config ()
test1unfold = Config {
                cTypes = [mPing (pvar "x"), mPong (pvar "x")]
              , cSets  = []
              , cUnfold = [Conc (S "ps") 1]
              , cProcs = [(tpid0,
                                Iter (V "pi") (S "ps")
                                        (Send (PVar (V "pi")) [(mPing tpid0, Recv [(mPong (pvar "x"), Skip ())] ())] ()) ())
                         ,(tpid2, Recv [(mPing (pvar "x"), Send (pvar "x") [(mPong tpid2, Skip ())] ())] ())]
}

-- ---

pingMany = Config {
             cTypes = [mPing (pvar "x"), mPong (pvar "x")]
           , cSets = []
           , cUnfold = [Conc (S "ps") 1]
           , cProcs = [( tpid0
                       , Block [ Iter (V "pi") (S "ps")
                                          (Send (pvar "pi") [(mPing tpid0, Skip ())] ()) ()
                                , Iter (V "pii") (S "ps")
                                          (Recv [(mPong (pvar "x"), Skip ())] ()) ()] ())
                      ,( tpid2
                       , Recv [(mPing (pvar "x"), Send (pvar "x") [(mPong (pvar "p"), Skip ())] ())] ())
                      ]
           }

-- ---

pingManyBad = Config {
             cTypes = [mPing (pvar "x"), mPong (pvar "x")]
           , cSets = []
           , cUnfold = [Conc (S "ps") 1]
           , cProcs = [( tpid0
                       , Block [ Iter (V "pi") (S "ps")
                                          (Send (pvar "pi") [(mPing tpid0, Skip ())] ()) ()
                                , Iter (V "pii") (S "ps")
                                          (Recv [(mPong (pvar "x"), Skip ())] ()) ()] ())
                      ,( tpid2
                       , Recv [(mPing (pvar "x"), Skip ())] ())
                      ]
           }

-- ---
mInt :: MType
mInt = MTApp (MTyCon "Int") []
masterSlave = Config {
                cTypes = [mInt]
              , cSets  = []
              , cUnfold = [Conc (S "ps") 1]
              , cProcs = [(tpid0, Iter (V "pi") (S "ps")
                                  (Recv [(mInt, Skip ())] ()) ())
                         ,(tpid2, Send tpid0 [(mInt, Skip ())] ())]
              }
-- ---
mPid :: Pid -> MType
mPid x = MTApp (MTyCon "Pid") [x]

mTT :: MType
mTT = MTApp (MTyCon "tt") []

mOK :: MType
mOK = MTApp (MTyCon "OK") []

proc_0, proc_1, proc_2 :: Stmt ()

proc_0 = Block [ Iter (V "pi") (S "ps")
                          (Recv [(mPid (pvar "x"), Send (pvar "x") [(mInt, Skip ())] ())] ()) ()
                , Loop (LV "end_X")
                          (Recv [(mPid (pvar "y"), Send (pvar "y") [(mTT, Goto (LV "end_X") ())] ())] ()) ()
                ]
         ()

proc_2 = Loop (LV "Y")
             (Send tpid0 [(mPid tpid2, Recv [(mInt, Send tpid1 [(mInt, Goto (LV "Y") ())] ())
                                              ,(mTT, Skip ())] ())] ()) ()
proc_1 = Iter (V "pi") (S "ps")
             (Recv [(mInt, Skip ())] ()) ()

workStealing :: Config ()
workStealing = Config {
                 cTypes = [mInt, mPid (pvar "x"), mTT]
               , cSets = []
               , cUnfold = [Conc (S "ps") 1]
               , cProcs = [(tpid0, proc_0)
                          ,(tpid1, proc_1)
                          ,(tpid2, proc_2)]
               }
-- ----

ssend p m r = Send p [(m, r)] ()
srecv m r   = Recv [(m, r)] ()
sloop x y   = Loop x y ()
siter x y z = Iter x y z ()
schoice x y z = Choose x y z ()

workPushing = Config {
                cTypes = [mInt]
              , cSets  = []
              , cUnfold = [Conc (S "ps") 1]
              , cProcs = [  (tpid0, Block [ siter (V "p") (S "ps")
                                                     (schoice (V "x") (S "ps") (ssend (pvar "x") mInt (Skip ())))
                                           , siter (V "pp") (S "ps")
                                                     (srecv mInt (Skip ()))
                                           ] ())
                          , (tpid2, sloop (LV "end_X") (srecv mInt (ssend tpid0 mInt (Goto (LV "end_X") ()))))
                          ]
              }

--

mutex :: Config ()
mutex = Config
        {
          cTypes  = [mPid (pvar "x"), mTT, mOK]
        , cSets   = []
        , cUnfold = [Conc (S "ps") 1]
        , cProcs  = [mutexMaster, mutexPs]
        }
  where
    mutexMaster  = (tpid0, mutexMasterS)
    mutexPs      = (tpid2, mutexPS)
    -- Master Process
    mutexMasterS :: Stmt ()
    mutexMasterS = Loop (LV "end_loop")
                   (Recv [(mPid (pvar "x"),
                                 Send (pvar "x") [(mTT,
                                                       Recv [(mOK, Goto (LV "end_loop") ())] ())] ())] ()) ()
    -- Slave Processes
    mutexPS :: Stmt ()
    mutexPS = Send tpid0 [(mPid tpid2, Recv [(mTT, Send tpid0 [(mOK, Skip ())] ())] ())] ()

mRelease :: Pid -> MType
mRelease v = MTApp (MTyCon "Rel") [v]

mutexBad :: Config ()
mutexBad = Config
        {
          cTypes  = [mPid (pvar "x"), mTT, mRelease (pvar "x")]
        , cSets   = []
        , cUnfold = [Conc (S "ps") 1]
        , cProcs  = [mutexMaster, mutexPs]
        }
  where
    mutexMaster  = (tpid0, mutexMasterS)
    mutexPs      = (tpid2, mutexPS)
    -- Master Process
    mutexMasterS :: Stmt ()
    mutexMasterS = Loop (LV "X")
                   (Recv [(mPid (pvar "x"),
                                 Send (pvar "x") [(mTT, Skip ())] ())] ()) ()
    -- Slave Processes
    mutexPS :: Stmt ()
    mutexPS = Send tpid0 [(mPid tpid2, Recv [(mTT, Skip ())] ())] ()

---
choiceBad :: Config ()
choiceBad
  = Config { cTypes = [mTT, mOK]
           , cUnfold = []
           , cSets   = []
           , cProcs = [ (tpid0, choiceMaster)
                      , (tpid1, choiceSlave)
                      ]
           }
    where
      choiceMaster = Send tpid1 [ (mTT, Send tpid1 [ (mTT, Skip ())
                                                     , (mOK, Skip ())
                                                     ] ())
                                 , (mOK, Send tpid1 [ (mTT, Skip ())
                                                     , (mOK, Skip ())
                                                     ] ())
                                   ] ()
      choiceSlave = Recv [ (mTT, Recv [ (mTT, Skip ()) ] ())
                          , (mOK, Recv [ (mOK, Skip ()) ] ())
                          ] ()

---
database :: Config ()
database = Config {
       cTypes = [ makeType0 "Set"
                , makeType0 "Value"
                , makeType1 "Get"
                ]
     , cSets = []
     , cUnfold = [Conc (S "ps") 1]
     , cProcs = [ (db, dbProc)
                , (ps, psProc)
                , (me, meProc)
                ]
     }
  where
    ps = PAbs (V "p") (S "ps")
    db = PConc 0
    me = PConc 1
    makeType0 t = MTApp (MTyCon t) []
    makeType1 t = MTApp (MTyCon t) [PVar (V "x")]
    val1 t v    = MTApp (MTyCon t) [v]

    psProc = Loop (LV "endX")
               (Recv [ (makeType0 "Set", Goto (LV "endX") ())
                      , (makeType1 "Get", Send (PVar (V "x")) [(makeType0 "Value", Goto (LV "endX") ())] ())
                      ] ())
               ()

    dbProc = Loop (LV "endX")
               (Recv [ (makeType0 "Set", Choose (V "y") (S "ps") (Send (PVar (V "y")) [(makeType0 "Set", Goto (LV "endX") ())] ()) ())
                      , (makeType1 "Get", Choose (V "y") (S "ps") (Send (PVar (V "y")) [(makeType1 "Get", Goto (LV "endX") ())] ()) ())
                      ] ())
               ()

    meProc = Loop (LV "endX")
               (Send db [ (makeType0 "Set", Goto (LV "endX") ())
                         , (val1 "Get" me, Recv [ (makeType0 "Value", Goto (LV "endX") ()) ] ())
                         ] ())
               ()

