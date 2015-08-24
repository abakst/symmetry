{-# LANGUAGE ScopedTypeVariables #-}
module Render where

import           Prelude hiding (concat, concatMap, sum, mapM, sequence, foldl, minimum, maximum)
import           Text.PrettyPrint.Leijen
import           Data.Function
import           Data.Foldable
import qualified Data.Map.Strict as M
import           Data.List (intercalate, groupBy, nub, partition)
import           Data.Generics hiding (empty)
import           Control.Exception
import           System.IO
import           Debug.Trace

import           AST  
  
debug msg x = 
  trace (msg ++ show x) x

-- | Some useful combinators
byte :: Doc                          
byte = text "byte"

setSize :: Int
setSize = infty
          
infty :: Int
infty = 2

($$) :: Doc -> Doc -> Doc
x $$ y = align (x <$> y)

atomic :: [Doc] -> Doc
atomic ss 
  = text "atomic" <+> block ss
    
block :: [Doc] -> Doc
block ds 
  = lbrace <$> (indent 2 $ seqStmts ds) <$> rbrace
    
ifs :: [Doc] -> Doc
ifs ss 
  = text "if" <$> (indent 2 $ nonDetStmts ss) <$> text "fi"
    
doLoop :: [Doc] -> Doc
doLoop ss
  = text "do" <$> (indent 2 $ nonDetStmts ss) <$> text "od" 
    
forLoop :: Doc -> Doc -> Doc
forLoop i body = text "for" <+> (parens i) <+> lbrace <$>
                 (indent 2 body) <$>
                 rbrace

nonDetStmts :: [Doc] -> Doc
nonDetStmts ss 
  = vcat $ map (text "::" <+>) ss

seqStmts :: [Doc] -> Doc
seqStmts ss = vcat . punctuate semi $ ss
         
-- | Rendering PIDs 
renderProcPrefix :: Pid -> Doc 
renderProcPrefix (PConc _)         = text "Conc_"
renderProcPrefix (PAbs _ (S s))    = text s
renderProcPrefix (PUnfold _ (S s) _) = text s
renderProcPrefix (PVar _)          = empty

renderProcName :: Pid -> Doc
renderProcName p@(PConc i)         = renderProcPrefix p <> int i
renderProcName p@(PAbs (V v) _)    = renderProcPrefix p <> brackets (text v)
renderProcName p@(PUnfold (V v) _ _) = renderProcPrefix p <> brackets (text v)
renderProcName p@(PVar (V v))      = renderProcPrefix p <> text v
                           
renderProcTypeName :: Pid -> Doc     
renderProcTypeName p@(PConc _)       = renderProcName p <> text "_Process"
renderProcTypeName p@(PAbs _ _)      = renderProcPrefix p <> text "_Process"
renderProcTypeName p@(PUnfold _ _ _)   = renderProcPrefix p <> 
                                       text "_Process_Unfold"

renderProcTypeArgs :: Pid -> Doc
renderProcTypeArgs (PConc _)          = parens empty
renderProcTypeArgs (PUnfold (V v) _ _) = parens (byte <+> text v)
renderProcTypeArgs (PAbs (V v) _)     = parens (byte <+> text v)

                                        
evalExp :: Doc -> Doc
evalExp e = text "eval" <> parens e

renderEvalPids  :: MType -> [Doc]
renderEvalPids
  = map go . tyargs
  where 
    go p@(PVar _) = renderProcName p
    go p@(PUnfold _ _ i) = evalExp (renderProcPrefix p <> brackets (int (i+setSize)))
    go p = evalExp (renderProcName p)

renderPids  :: MType -> [Doc]
renderPids
  = map renderProcName . tyargs

-- | Messages
renderMType :: MType -> Doc
renderMType 
  = text . untycon . tycon
    
renderSendMsg :: MType -> Doc
renderSendMsg m@(MTApp _ [])
  = renderMType m
renderSendMsg m
  = renderMType m <> tupled (renderPids m)
             
renderRecvMsg :: MType -> Doc 
renderRecvMsg m@(MTApp _ [])
  = renderMType m 
renderRecvMsg m
  = renderMType m <> tupled (renderEvalPids m)

renderMTypes :: [MType] -> Doc
renderMTypes ts
  = text "mtype" 
    <+> equals
    <+> encloseSep lbrace rbrace comma rts
    <> semi
  where
    rts = map renderMType ts
          
-- | Addressing Process Channels
renderSwitchboard :: Int -> Int -> Doc
renderSwitchboard nprocs ntypes = text "chan" <+> text "switchboard" 
                                  <+> brackets (int (nprocs*nprocs*ntypes))
                                  <> semi
             
switchboard :: Int -> Int -> Pid -> Pid -> MType -> Doc 
switchboard np nt from p m = 
  -- text "switchboard" <+> brackets (
                          (renderProcVar from <> text "*" <> int (np*nt))
                          <+> text "+"
                          <+> (renderProcVar p <> text "*" <> int nt)
                          <+> text "+"
                          <+> parens (renderMType m <> text "-" <> int 1)
                         -- )

initSwitchboard :: Int -> Int -> Pid -> Pid -> MType -> Doc
initSwitchboard np nt p q t
  = text "switchboard" <> 
    brackets (switchboard np nt p q t) <+> 
    equals <+> 
    renderChanName p q t 
               
-- initSwitchboard n p@(PAbs (V v) (S _)) t
--   = forLoop (text v <+> text "in" <+> renderProcPrefix p) $
--     (switchboard n p t <+> equals <+> renderChanName p q t <> brackets (text v))

renderChanName :: Pid -> Pid -> MType -> Doc                            
renderChanName p q t
  =  renderProcChanName p <> text "_" <>
     renderProcChanName q <> text "_" <>
     renderMType t
       where
         renderProcChanName p@(PConc _)
           = renderProcName p
         renderProcChanName p@(PAbs _ _) 
           = renderProcPrefix p
         renderProcChanName p@(PUnfold _ _ i) 
           = renderProcPrefix p <> text "_Unfold" <> int i
                                   
renderProcDecl :: Doc -> Doc     
renderProcDecl n
  = byte <+> n
    
renderProcAssn :: Doc -> Doc -> Doc
renderProcAssn n rhs 
  = renderProcDecl n <+> equals <+> rhs
    
type SetMap  = M.Map Set Int
type ChanMap = Pid -> Pid -> MType -> Doc

-- | Emit Promela code for each statement    
renderStmt :: ChanMap -> PidMap -> SetMap -> Pid -> Stmt Int -> Doc
renderStmt f pm sm (p @ (PConc _)) s       = renderStmtConc f pm sm p s
renderStmt f pm sm (p @ (PUnfold _ _ _)) s = renderStmtConc f pm sm p s
renderStmt f pm sm p s                     = renderStmtAbs  f pm sm cfg p s
  where
    cfg = nextStmts s
-- renderStmt f p s               = nonDetStmts $ map (renderStmtAbs f p) ss
--   where
--     ss = listify (\(_::Stmt Int) -> True) s
        
sendMsg :: ChanMap -> Pid -> Pid -> MType -> Doc 
sendMsg f p q m
  = text "switchboard" <> brackets (f p q m) <> text "!" <> renderSendMsg m

recvMsg :: ChanMap -> Pid -> Pid -> MType -> Doc 
recvMsg f p q m
  = text "__RECV" <> tupled [f p q m , renderRecvMsg m]
                   
renderStmtConc :: ChanMap -> PidMap -> SetMap -> Pid -> Stmt Int -> Doc
renderStmtConc f pm sm me (SSend p [(m,s)] _)
  = align (sendMsg f me p m <> semi <$>
           renderStmt f pm sm me s)
renderStmtConc f pm sm me (SSend p ms _)
  = ifs $ map go ms
  where 
    go (m, s) = 
      case s of
        SSkip _ -> 
          sendMsg f me p m
        _       ->
          block [ sendMsg f me p m, renderStmt f pm sm me s ]
      
renderStmtConc f pm sm me (SRecv [(m,s)] _)
  = align (ifs recvs <> semi <$>
           renderStmt f pm sm me s)
  where
    recvs = map go $ M.keys pm
    go p  = recvMsg f p me m

renderStmtConc f pm sm me (SRecv ms _)
  = ifs (concatMap recvs ms)
  where 
    recvs (m, s) = map (go m s) $ M.keys pm
    go m s p = 
      case s of 
        SSkip _ -> 
          recvMsg f p me m
        _       -> 
          seqStmts [recvMsg f p me m, renderStmt f pm sm me s]          
renderStmtConc _ _ _ _ (SSkip _)
  = text "skip"
    
renderStmtConc f pm sm me (SIter (V v) (S s) ss _)
  = byte <+> text ("__" ++ v) <> semi <$>
    forLoop (text ("__" ++ v) <+> text "in" <+> text s)
            (text v <+> equals <+> renderProcName (PAbs (V ("__" ++ v)) (S s)) <> semi <$>
             renderStmt f pm sm me ss)
        
renderStmtConc f pm sm me (SLoop (LV v) ss _)
  = text v <> text ":" <$> renderStmt f pm sm me ss
     
renderStmtConc _ _ _ _ (SVar (LV v) _)
  = text "goto" <+> text v 
    
renderStmtConc f pm sm me (SChoose (V v) s ss _)
  = block [ text "select" <+> 
            parens (text v <+> text ":" <+> int 0 <+> text ".." <+> sz)
          , renderProcName (PVar (V v)) <+> equals <+> renderProcName (PAbs (V v) s)
          , renderStmt f pm sm me ss
          ]
  where
    sz  = maybe err int $ M.lookup s sm
    err = error ("Unknown set (renderStmtConc): " ++ show s)
    
renderStmtConc f pm sm me (SBlock ss _)
  = block $ map (renderStmt f pm sm me) ss
          
renderStmtConc _ _ _ _ _
  = text "assert(0 == 1) /* TBD */"
 
stmtLabel :: Int -> Doc 
stmtLabel i = 
  text "stmt_L" <> int i 

label :: Doc -> Doc -> Doc       
label l d =
  l <> text ":" <+> d

labelStmt :: Int -> Doc -> Doc
labelStmt i s
  = label (stmtLabel i) s
   
stmtGuard :: Int -> Doc 
stmtGuard i
  = stmtCounter i <+> text ">" <+> int 0
    
inOutCounters :: M.Map Int [Int]
              -> Int
              -> [Doc]
inOutCounters cfg i
  = case outCounters cfg i of
      []  -> [decrCounter i]
      ocs -> decrCounter i : ocs
                 
outCounters :: M.Map Int [Int]
              -> Int
              -> [Doc]
outCounters cfg i
  = case M.lookup i cfg of
      Nothing -> []
      Just js -> map incrCounter js

renderStmtAbs :: ChanMap 
              -> PidMap
              -> SetMap
              -> (M.Map Int [Int])
              -> Pid 
              -> Stmt Int 
              -> Doc
renderStmtAbs f pm sm cfg me (SSend p ms i)
  = block (recv : ctrs)
  where
    recv = renderStmtConc f pm sm me (SSend p [(mt, SNull) | (mt,_) <- ms] i)
    ctrs = inOutCounters cfg i
    
renderStmtAbs f pm sm cfg me (SRecv ms i)
  = ifs ( {- text "skip" : -} [ render1 (mt, SNull) oc | ((mt,_), oc) <- outms] )
  where
    outms = assert (length ms == length outcs) $ zip ms outcs
    outcs = outCounters cfg i
    render1 m oc = {- recvGuard f me [m] <+> text "->" <$> -}
                      block ((renderStmtConc f pm sm me $ SRecv [m] i) : [decrCounter i, oc])
                            
renderStmtAbs _ _ _ cfg _ (SVar _ i)
  = block (inOutCounters cfg i)
       
renderStmtAbs _ _ _ cfg _ (SSkip i)
  = block (inOutCounters cfg i) 
   
renderStmtAbs _ _ _ cfg _ (SLoop _ _ i)
  = block (inOutCounters cfg i)

renderStmtAbs _ _ _ _ _ (SNull)
  = text "skip"

renderStmtAbs _ _ _ _ _ s
  = text $ "assert(0 == 1) /* TBD:" ++ show s
   
nonDetSkip :: Int -> Doc 
nonDetSkip i
  = labelStmt i $
    ifs [ stmtCounter i <+> text ">" <+> int 0 <+> text "->" <+> text "skip"
        , gotoStmt (i + 1)
        ]

stmtCounter :: Int -> Doc
stmtCounter i
  = text "k_" <> int i
    
decrCounter :: Int -> Doc
decrCounter i
  = text "__DEC" <> parens (stmtCounter i) <> semi <$>
    text "from" <+> equals <+> int i 

incrCounter :: Int -> Doc
incrCounter i
  = text "__INC" <> parens (stmtCounter i) <> semi <$>
    text "to" <+> equals <+> int i
    
gotoStmt :: Int -> Doc
gotoStmt i
  = text "goto" <+> stmtLabel i

-- recvGuard :: ChanMap -> Pid -> Pid -> [(MType, a)] -> Doc
-- recvGuard f them me ms
--   = (hcat $ punctuate (text "||") (map go ms))
--   where
--     go (m, _) = text "nempty" <> parens (f them me m)
               
selectStmt :: [Int] -> Doc 
selectStmt is 
  = ifs $ map goto is
    where
      goto :: Int -> Doc
      goto i = seqStmts 
               [ stmtGuard i
               , gotoStmt i
               ]

(<?$>) :: [Doc] -> Doc -> Doc
[] <?$> y = y
xs <?$> y = vcat xs <$> y

renderProcStmts :: ChanMap -> PidMap -> SetMap -> Process Int -> Doc
renderProcStmts f pm m (p, ss) 
  = [ byte <+> text v <> semi | (V v) <- recvVars vs ] <?$> 
    if isAbs p then
      -- cvs <$>
      (labelStmt 0 .
         (text "from" <+> equals <+> int 0 <> semi <$>) .
         (text "to" <+> equals <+> int 0 <> semi <$>) .
         selectStmt $ foldl' (flip (:)) [] ss) <$>
      (label (text "end") $ text "0" <> semi) <$>
      (seqStmts . map do1Abs $ listify notNull ss)
      -- label (text "end") $
      --   doLoop $ 
      --     map (atomic . return . renderStmt f m p) $ listify notSkip ss
    else
      renderStmt f pm m p ss <> semi <$>
      label (text "end") (text "0")
  where
    do1Abs s = labelStmt (annot s) $ 
                  atomic [renderStmt f pm m p s, gotoStmt 0]
    notNull SNull       = False
    notNull _           = True
    recvVars                = filter (not . isProcVar p) . nub
    isProcVar (PAbs v _) v'    = v == v'
    isProcVar (PUnfold v _ _) v' = v == v'
    isProcVar _          _  = False
    vs                      = listify go ss :: [Var]
    go :: Var -> Bool
    go                      = const True
  
renderProc :: ChanMap -> PidMap -> SetMap -> Process Int -> Doc
renderProc f pm m p
  = (if (isAbs (fst p)) then
      text "/* Counters for" <+> renderProcTypeName (fst p) <+> text "*/" <$>
      cvs 
    else
      empty) <$>
    text "proctype" <+>
           renderProcTypeName (fst p) <+>
           renderProcTypeArgs (fst p) <$>
           block [ renderProcStmts f pm m p ]
  where
    cs                      = foldl' (flip (:)) [] (snd p)
    cvs                     = if isAbs (fst p) then
                                byte <+> 
                                  stmtCounter (cs !! 0) <+> 
                                  equals <+> 
                                  text "__K__" <> semi <$>
                                vcat [ byte <+> 
                                       stmtCounter c <> 
                                       semi | c <- nub $ tail cs ]
                              else
                                empty

renderProcs :: Config Int -> PidMap -> SetMap -> Doc
renderProcs (Config { cTypes = ts, cProcs = ps }) pm m
  = foldl' (\d p -> d <$$> render1 p) empty psfilter
  where
    render1 = renderProc (switchboard (length ps) (length ts)) pm m
    -- For each unfolded process, it suffices to 
    -- render the body once
    psfilter = map head $ groupBy (eqUnfolds `on` fst) ps
    eqUnfolds (PUnfold v s _) (PUnfold v' s' _) = v == v' && s == s'
    eqUnfolds p1 p2 = p1 == p2
    
renderMain :: PidMap -> Config a -> Doc
renderMain m (Config { cTypes = ts, cProcs = ps})
  = text "init" <+> block body
  where
    body        = declAbsVars ++
                  [ atomic pidInits
                  , atomic boardInits
                  , atomic procInits
                  ]
    declAbsVars = [ byte <+> text v | PAbs (V v) _ <- map fst ps ]
    boardInits  = do let pids = map fst ps
                     p        <- pids
                     q        <- pids
                     t        <- ts
                     return $ initSwitchboard (length ps) (length ts) p q t
    procInits   = map (runProc m . fst) ps
    pidInits    = map ((\p -> assignProcVar p (sz p)) . fst) ps
    sz p        = maybe (err p) id $ M.lookup p m
    err p       = error ("Unknown pid (renderMain): " ++ show p)

runProc :: PidMap -> Pid -> Doc
runProc _ p@(PConc _) 
  = text "run" <+> 
    renderProcTypeName p <>
    parens empty

runProc _ p@(PAbs _ _)
  = text "run" <+> renderProcTypeName p <> parens (int 0)
  where
              
runProc _ p@(PUnfold _ _ i)
  = text "run" <+> renderProcTypeName p <> parens (int (setSize + i))
    
renderProcVar :: Pid -> Doc
renderProcVar (PAbs _ (S s))
  = text s <> brackets (int 0)
renderProcVar p@(PUnfold _ _ _)
  = unfoldProcVar p
renderProcVar p
  = renderProcName p

assignProcVar :: Pid -> (Int, Int) -> Doc                  
assignProcVar p@(PConc _) (i, _)
  = renderProcVar p <+> equals <+> (int i)
assignProcVar (PAbs _ (S s)) (i, sz)
  = seqStmts $ map (uncurry go) (zip [0..setSize-1] (repeat i) ++
                                 zip [setSize..sz-1] [(i+1)..(i+sz-setSize)])
  where
    go j k = text s <> brackets (int j) <+> equals <+> int k

assignProcVar p@(PUnfold _ _ i) (v, _)
  = unfoldProcVar p <+> equals <+> int (v + i)

unfoldProcVar :: Pid -> Doc
unfoldProcVar p@(PUnfold _ _ i)
  = renderProcPrefix p <> text "Unfold_" <> int i

declProcVar :: Pid -> (Int, Int) ->  Doc             
declProcVar p@(PConc _) _
  = renderProcDecl (renderProcName p) <> semi
declProcVar p@(PAbs (V _) (S _)) (_, sz)
  = renderProcDecl (renderProcPrefix  p) <> brackets (int sz) <> semi
declProcVar p@(PUnfold (V _) (S _) _) _
  = renderProcDecl (unfoldProcVar p) <> semi 
             
declProcVars :: PidMap -> Doc
declProcVars m
  = M.foldrWithKey go empty m
  where
    go pid k d = declProcVar pid k <$> d
                
chanMsgType :: MType -> Doc
chanMsgType t
  = enclose lbrace rbrace . hcat $ punctuate comma msg 
    where
      msg =  text "mtype" : map (const (byte)) (tyargs t)
             
declChannels :: PidMap -> [MType] -> Doc
declChannels pm ts 
  = vcat $ map (\t -> vcat $ map (go t) (product $ M.keys pm)) ts
  where
    product ps = [ (p,q) | p <- ps, q <- ps ]
    go t (p,q)           = text "chan" <+> renderChanName p q t
                               <+> equals
                               <+> text "[__K__] of"
                               <+> chanMsgType t
                               <> semi
    -- go t p@(PConc _)  = text "chan" <+> renderChanName p q t
    --                            <+> equals
    --                            <+> text "[1] of"
    --                            <+> chanMsgType t
    --                            <> semi
    -- go t p@(PAbs _ _) = text "chan" <+> renderChanName p q t <> brackets (int (sz p))
    --                            <+> equals
    --                            <+> text "[1] of"
    --                            <+> chanMsgType t
    --                            <> semi
    -- go _ (PUnfold _ _ _)= empty
    sz p                = maybe (err p) snd $ M.lookup p pm
    err p               = error ("Unknown pid (runProc): " ++ show p)

buildPidMap :: Config a -> PidMap
buildPidMap (Config { cUnfold = us, cProcs = ps })
  = fst $ foldl' go (foldl' go (M.empty, 0) (snd pids)) (fst pids)
  where 
    pids                      = partition isUnfold $ map fst ps
    go (m, i) p@(PConc _)     = (M.insert p (i, 1) m, succ i)
    go (m, i) p@(PAbs _ set)  = let s = setSize + unfolds set
                                in (M.insert p (i, s) m, i + s)
    go (m, i) p@(PUnfold _ _ _) = updUnfold (m, i) p
    unfolds s                 = sum $ [ x | Conc s' x <- us, s == s' ]
                             
updUnfold :: (PidMap, Int) -> Pid -> (PidMap, Int)
updUnfold (m, i) p@(PUnfold v s _)
  = (M.insertWith upd p (j, 1) m, i)
    where
      upd (a,b) (_,d) = (a, b+d)
      j               = maybe err (succ . fst) $ M.lookup (PAbs v s) m
      err             = error ("Unknown pid (updUnfold): " ++ show p)

declSwitchboard :: PidMap -> [MType] -> Doc
declSwitchboard pm ts
  = renderSwitchboard nprocs (length ts)
    where 
      nprocs = M.foldrWithKey (\p v s -> s + count p v) 0 pm
      count (PAbs _ _) (_, n) = n - setSize + 1
      count (PConc _) (_,n) = n
      count _ _          = 0

macrify = intercalate " \\\n"
decMacro = macrify [ "#define __DEC(_x) atomic { assert (_x > 0);"
                   , "if"
                   , ":: (_x < __K__) ->  _x = _x - 1"
                   , ":: else; {"
                   , "if"
                   , ":: _x = _x - 1"
                   , ":: skip" 
                   , "fi }"
                   , "fi }"
                   ]
recvMacro =
  macrify [ "#define __RECV(_i, _as) atomic {"
          , "switchboard[_i]?[_as];"
          , "if"
          , "  :: len(switchboard[_i]) < __K__ ->"
          , "     switchboard[_i]?_as"
          , "  :: else ->"
          , "  if"
          , "  :: switchboard[_i]?_as"
          , "  :: switchboard[_i]?<_as>"
          , "  fi"
          , "fi }"
          ]
                           
macros :: [Doc]
macros = 
  [ text "#define __K__" <+> int infty
  , text "#define __INC(_x) _x = (_x < __K__ -> _x + 1 : _x)"
  , text decMacro
  , text recvMacro
  -- , text "#define __DEC(_x) assert (_x > 0); if :: _x < __K__ -> _x = _x - 1 :: else -> if :: _x = _x - 1 :: skip fi fi"
  -- , text "#define __RECV(_i, _args) if :: len(switchboard[_i]) < __K__ -> switchboard[_i]?_args :: else -> if :: switchboard[_i]?<_args> :: switchboard[_i]?_args fi fi"
  ]
  
render :: Show a => Config a -> Doc
render c@(Config { cTypes = ts })
  = mtype
    <$$> (align $ vcat macros)
    <$$> (byte <+> text "to" <> semi)
    <$$> (byte <+> text "from" <> semi)
    <$$> declProcVars pidMap
    <$$> declChannels pidMap ts
    <$$> declSwitchboard pidMap ts
    <$$> procs
    <$$> renderMain pidMap unfolded
  where
    unfolded                 = freshIds . instAbs $ unfold c
    pidMap                   = buildPidMap unfolded
    mtype                    = renderMTypes ts
    procs                    = renderProcs (unfolded) pidMap setMap
    setMap                   = M.foldrWithKey goKey M.empty pidMap
    goKey (PAbs _ s) (_,n) m = M.insert s n m
    goKey _          _     m = m

renderToFile :: Show a => FilePath -> Config a -> IO ()
renderToFile fn c
  = withFile fn WriteMode $ flip hPutDoc (render c)
    
renderToFileVC :: Show a => FilePath -> Config a -> IO ()
renderToFileVC fn c
  = do renderToFile fn c
       withFile (fn ++ ".ltl") WriteMode $ flip hPutDoc (vcGen c)

always, eventually, lneg :: Doc -> Doc
always x     = text "[]" <+> parens x
eventually x = text "<>" <+> parens x
lneg x       = text "!" <+> parens x 
               
impl :: Doc -> Doc -> Doc
impl x y     = parens x <+> text "->" <+> parens y
               
vcGen :: Config a -> Doc
vcGen c
  = lneg $ impl (fairness c') (eventually $ endCondition c')
  where c' = freshIds $ unfold c
               
endCondition :: Config Int -> Doc
endCondition c
  = vcat $ punctuate (text "&&") es
  where
    es = [ parens . hcat $ punctuate (text "||") (conds p s)
         | (p, s) <- cProcs c, not (isAbs p) ]
    conds p s =
      (pn p <> text "@end") 
       : [pn p <> text "@" <> (text $ unlv s) | s <- endLabels s]
    pn p = renderProcTypeName p

               
fairness :: Config Int -> Doc
fairness c
  = vcat $ punctuate (text "&&") (js ++ cs)
  where
    js = concat [ stmtJustice s | (PAbs _ _, s) <- cProcs c ]
    cs = concat [ stmtCompassion s | (PAbs _ _, s) <- cProcs c ]
         
syncPairs c
  = (concRWs, absWRs)
  where
    -- foo     = map (syncMatch concRWs) absWRs
    absWRs  = [ (p, wrPairs s) | (p@(PAbs _ _), s) <- cProcs c ]
    concRWs = [ (p, rwPairs s) | (p, s) <- cProcs c, not $ isAbs p ]
              
-- syncMatch rws (p, wrs)
--   = undefined
--     where
--       rwList     = snd rws
--       matchWRRW (t1,p1,u1) (t2,p2,u2) = tycon t1 == tycon t2 &&
                                        
--       candidates = [ (q, (t1, p, t2)) | (q, tpts) <- rws, (t1,p',t2) <- 

stmtJustice :: Stmt Int -> [Doc]
stmtJustice s 
  = map justice rs
  where
    justice e = parens (always . eventually . lneg $ gtz (stmtCounter $ annot e))
    gtz x     = x <+> rangle <+> int 0
    rs :: [Stmt Int]
    rs = nub $ listify (\s -> case s of
                                SSend _ _ _ -> True
                                _           -> False) s
                                     
stmtCompassion :: Stmt Int -> [Doc]
stmtCompassion s
  = map compassion ss
  where
    compassion e = parens (impl (always . eventually $ eqFrom (annot e))
                                (always . eventually $ eqTo (annot e)))
    eqFrom i     = text "from" <+> eq <+> int i
    eqTo i       = text "to" <+> eq <+> int i
    eq           = equals <> equals
    ss           = nub $ listify isRecv s
    isRecv :: Stmt Int -> Bool
    isRecv (SRecv _ _) = True
    isRecv _           = False
