module Tests where
import AST
import Render

-- t0 = Config { cTypes = [ MTApp (MTyCon "PING") [PVar (V "x")]
--                   , MTApp (MTyCon "PONG") [PVar (V "x")]
--                   ]
  
--        , cSets  = []

--        , cProcs = [(PConc 0, 
--                    [ SChoose (V "pi") (S "ps") 
--                        [SSend (PVar (V "pi")) [(MTApp (MTyCon "PING") [PConc 0], 
--                                                         [SRecv [(MTApp (MTyCon "PONG") [PVar (V "x")], [])] ()])] ()] ()]),
--             (PAbs (V "p") (S "ps"),
--              [SLoop (V "X")
--                       [SRecv [(MTApp (MTyCon "PING") [PVar (V "x")], 
--                               [SSend (PVar (V "x")) [(MTApp (MTyCon "PONG") [PVar (V "x")], [SVar (V "X") ()])] ()])] ()] ()])]
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
          cTypes = [mPing (pvar "x"), mPong (pvar "x"), MTApp (MTyCon "Unit") []]
        , cSets  = []
        , cUnfold = []
        , cProcs = [(tpid0, SSend tpid1 [(mPing tpid0, SRecv [(mPong (pvar "x"), SSkip ())] ())] ())
             ,(tpid1, SRecv [(mPing (pvar "x"), SSend (pvar "x") [(mPong tpid1, SSkip ())] ())] ())]
} :: Config ()

-- test0a = Config {
--   cTypes = [mPing (pvar "x"), mPong (pvar "x"), MTApp (MTyCon "Unit") []]
--   , cSets  = []
--   , cProcs = [(tpid0, 
--                     [SLoop (V "X")
--                       [SSend tpid1 [(mPing tpid0, [SRecv [(mPong (pvar "x"), [SVar (V "X") ()])] ()])] ()] ()])
--              ,(tpid1, 
--                     [SLoop (V "Y")
--                       [SRecv [(mPing (pvar "x"), [SSend (pvar "x") [(mPong tpid1, [SVar (V "Y") ()])] ()])] ()] ()])]
-- }

test1 :: Config ()
test1= Config {
         cTypes = [mPing (pvar "x"), mPong (pvar "x"), MTApp (MTyCon "Unit") []]
       , cSets  = []
       , cUnfold = [] 
  , cProcs = [(tpid0, 
                SIter (V "pi") (S "ps") 
                  (SBlock [SSend (PVar (V "pi")) [(mPing tpid0, SRecv [(mPong (pvar "x"), SSkip ())] ())] ()] ()) ())
             ,(tpid2, SRecv [(mPing (pvar "x"), SSend (pvar "x") [(mPong tpid2, SSkip ())] ())] ())]
}

test1unfold :: Config ()
test1unfold = Config {
                cTypes = [mPing (pvar "x"), mPong (pvar "x")]
              , cSets  = []
              , cUnfold = [Conc (S "ps") 1]
              , cProcs = [(tpid0, 
                                SIter (V "pi") (S "ps") 
                                        (SSend (PVar (V "pi")) [(mPing tpid0, SRecv [(mPong (pvar "x"), SSkip ())] ())] ()) ())
                         ,(tpid2, SRecv [(mPing (pvar "x"), SSend (pvar "x") [(mPong tpid2, SSkip ())] ())] ())]
}

-- ---

-- pingMany = Config { 
--              cTypes = [mPing (pvar "x"), mPong (pvar "x")]
--            , cSets = []
--            , cProcs = [( tpid0
--                        , [ SIter (V "pi") (S "ps")
--                                    [SSend (pvar "pi") [(mPing tpid0, [])] ()] ()
--                          , SIter (V "pii") (S "ps")
--                                    [SRecv [(mPong (pvar "x"), [])] ()] ()])
--                       ,( tpid2
--                        , [SRecv [(mPing (pvar "x"), [SSend (pvar "x") [(mPong (pvar "p"), [])] ()])] ()])
--                       ]
--            }
            
-- ---
mInt :: MType
mInt = MTApp (MTyCon "Int") []
-- masterSlave = Config {
--                 cTypes = [mInt]
--               , cSets  = []
--               , cProcs = [(tpid0,
--                           [SIter (V "pi") (S "ps")
--                                   [SRecv [(mInt, [])] ()] ()])
--                          ,(tpid2,
--                            [SSend tpid0 [(mInt, [])] ()])]
--               }
-- --- 
mPid :: Pid -> MType
mPid x = MTApp (MTyCon "Pid") [x]

mTT :: MType
mTT = MTApp (MTyCon "tt") []

mOK :: MType
mOK = MTApp (MTyCon "OK") []
      
proc_0, proc_1, proc_2 :: Stmt ()
         
proc_0 = SBlock [ SIter (V "pi") (S "ps") 
                          (SRecv [(mPid (pvar "x"), SSend (pvar "x") [(mInt, SSkip ())] ())] ()) ()
                , SLoop (LV "end_X") 
                          (SRecv [(mPid (pvar "y"), SSend (pvar "y") [(mTT, SVar (LV "end_X") ())] ())] ()) ()
                ] 
         ()

proc_2 = SLoop (LV "Y")
             (SSend tpid0 [(mPid tpid2, SRecv [(mInt, SSend tpid1 [(mInt, SVar (LV "Y") ())] ())
                                              ,(mTT, SSkip ())] ())] ()) ()
proc_1 = SIter (V "pi") (S "ps")
             (SRecv [(mInt, SSkip ())] ()) ()

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

-- ssend p m r = SSend p [(m, r)] ()
-- srecv m r   = SRecv [(m, r)] ()
-- sloop x y   = SLoop x y ()
-- siter x y z = SIter x y z ()
-- schoice x y z = SChoose x y z ()
            
-- workPushing = Config {
--                 cTypes = [mInt]
--               , cSets  = []
--               , cProcs = [  (tpid0, [ siter (V "p") (S "ps")
--                                             [schoice (V "x") (S "ps") [ssend (pvar "x") mInt []]]
--                                     , siter (V "pp") (S "ps")
--                                             [srecv mInt []]
--                                   ])
--                           , (tpid2, [ sloop (V "X: end") [srecv mInt [ssend tpid0 mInt []], SVar (V "X") ()] ])
--                           ]
--               }

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
    mutexMasterS = SLoop (LV "end_loop")
                   (SRecv [(mPid (pvar "x"), 
                                 SSend (pvar "x") [(mTT,
                                                       SRecv [(mOK, SVar (LV "end_loop") ())] ())] ())] ()) ()
    -- Slave Processes
    mutexPS :: Stmt ()
    mutexPS = SSend tpid0 [(mPid tpid2, SRecv [(mTT, SSend tpid0 [(mOK, SSkip ())] ())] ())] ()

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
    mutexMasterS = SLoop (LV "X")
                   (SRecv [(mPid (pvar "x"), 
                                 SSend (pvar "x") [(mTT, SSkip ())] ())] ()) ()
    -- Slave Processes
    mutexPS :: Stmt ()
    mutexPS = SSend tpid0 [(mPid tpid2, SRecv [(mTT, SSkip ())] ())] ()

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
      choiceMaster = SSend tpid1 [ (mTT, SSend tpid1 [ (mTT, SSkip ())
                                                     , (mOK, SSkip ())
                                                     ] ())
                                 , (mOK, SSend tpid1 [ (mTT, SSkip ())
                                                     , (mOK, SSkip ())
                                                     ] ())
                                   ] ()
      choiceSlave = SRecv [ (mTT, SRecv [ (mTT, SSkip ()) ] ())
                          , (mOK, SRecv [ (mOK, SSkip ()) ] ())
                          ] ()
