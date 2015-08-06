{-# LANGUAGE ScopedTypeVariables #-}
module Render where

import           Prelude hiding (sum, mapM, sequence, foldl)
import           Text.PrettyPrint.Leijen
import           Data.Function
import           Data.Foldable 
import qualified Data.Map.Strict as M
import           Data.List (groupBy, nub, partition)
import           Data.Generics hiding (empty)
import           Control.Exception

import           AST  

-- | Some useful combinators
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
renderProcTypeArgs (PUnfold (V v) _ _) = parens (text "int" <+> text v)
renderProcTypeArgs (PAbs (V v) _)     = parens (text "int" <+> text v)

renderPids  :: MType -> [Doc]
renderPids
  = map renderProcName . tyargs

-- | Messages
renderMType :: MType -> Doc
renderMType 
  = text . untycon . tycon
             
renderMsg :: MType -> Doc 
renderMsg m 
  = hcat $ punctuate comma (renderMType m : renderPids m)

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
renderSwitchboard m n = text "chan" <+> text "switchboard" 
                                    <+> brackets (int (m * n))
                                    <> semi
             
switchboard :: Int -> Pid -> MType -> Doc 
switchboard np p m = 
  text "switchboard" <+> brackets (
                          (renderProcName p <> text "*" <> int np)
                          <+> text "+"
                          <+> parens (renderMType m <> text "-" <> int 1)
                         )

initSwitchboard :: Int -> Pid -> MType -> Doc
initSwitchboard n p@(PConc _) t
  = switchboard n p t <+> equals <+> renderChanName p t 
               
initSwitchboard n p@(PAbs (V v) (S _)) t
  = forLoop (text v <+> text "in" <+> renderProcPrefix p) $
    (switchboard n p t <+> equals <+> renderChanName p t <> brackets (text v))

renderChanName :: Pid -> MType -> Doc                            
renderChanName p@(PConc _) t 
  = renderProcName p <> text "_" <> renderMType t
renderChanName p@(PAbs _ _) t 
  = renderProcPrefix p <> text "_" <> renderMType t
                                   
renderProcDecl :: Doc -> Doc     
renderProcDecl n
  = text "int" <+> n
    
renderProcAssn :: Doc -> Doc -> Doc
renderProcAssn n rhs 
  = renderProcDecl n <+> equals <+> rhs
    
type PidMap  = M.Map Pid (Int, Int)
type SetMap  = M.Map Set Int
type ChanMap = Pid -> MType -> Doc

-- | Emit Promela code for each statement    
renderStmt :: ChanMap -> SetMap -> Pid -> Stmt Int -> Doc
renderStmt f pm (p @ (PConc _)) s     = renderStmtConc f pm p s
renderStmt f pm (p @ (PUnfold _ _ _)) s = renderStmtConc f pm p s
renderStmt f pm p s                   = renderStmtAbs  f pm cfg p s
  where
    cfg = nextStmts s
-- renderStmt f p s               = nonDetStmts $ map (renderStmtAbs f p) ss
--   where
--     ss = listify (\(_::Stmt Int) -> True) s
        
sendMsg :: ChanMap -> Pid -> MType -> Doc 
sendMsg f p m
  = f p m <> text "!" <> renderMsg m

recvMsg :: ChanMap -> Pid -> MType -> Doc 
recvMsg f p m
  = f p m <> text "?" <> renderMsg m
                   
renderStmtConc :: ChanMap -> SetMap -> Pid -> Stmt Int -> Doc
renderStmtConc f pm me (SSend p [(m,s)] _)
  = align (sendMsg f p m <> semi <$>
           renderStmt f pm me s)
renderStmtConc f pm me (SSend p ms _)
  = ifs $ map go ms
  where 
    go (m, s) = 
      text "::"  <+>
      case s of
        SSkip _ -> 
          sendMsg f p m
        _       ->
          block [ sendMsg f p m, renderStmt f pm me s ]
      
renderStmtConc f pm me (SRecv [(m,s)] _)
  = align (recvMsg f me m <> semi <$>
           renderStmt f pm me s)
renderStmtConc f pm me (SRecv ms _)
  = text "if"
      $$ vcat (map go ms)
    <$> text "fi"
  where 
    go (m, s) = 
      text "::" <+> 
      case s of 
        SSkip _ -> recvMsg f me m
        _       -> seqStmts [recvMsg f me m, renderStmt f pm me s]
          
renderStmtConc _ _ _ (SSkip _)
  = text "skip"
    
renderStmtConc f pm me (SIter (V v) (S s) ss _)
  = text "int" <+> text ("__" ++ v) <> semi <$>
    forLoop (text ("__" ++ v) <+> text "in" <+> text s)
            (text v <+> equals <+> renderProcName (PAbs (V ("__" ++ v)) (S s)) <> semi <$>
             renderStmt f pm me ss)
        
renderStmtConc f pm me (SLoop (V v) ss _)
  = text v <> text ":" <$> renderStmt f pm me ss
     
renderStmtConc _ _ _ (SVar (V v) _)
  = text "goto" <+> text v 
    
renderStmtConc f pm me (SChoose (V v) s ss _)
  = block [ text "select" <+> 
            parens (text v <+> text ":" <+> int 0 <+> text ".." <+> sz)
          , renderProcName (PVar (V v)) <+> equals <+> renderProcName (PAbs (V v) s)
          , renderStmt f pm me ss
          ]
  where
    sz  = maybe err int $ M.lookup s pm
    err = error ("Unknown set (renderStmtConc): " ++ show s)
    
renderStmtConc f pm me (SBlock ss _)
  = block $ map (renderStmt f pm me) ss
          
renderStmtConc _ _ _ _
  = text "assert(0 == 1) /* TBD"
 
stmtLabel :: Int -> Doc 
stmtLabel i = 
  text "stmt_L" <> int i 

label :: Doc -> Doc -> Doc       
label l d =
  l <> text ":" <+> d

labelStmt :: Int -> Doc -> Doc
labelStmt i s
  = label (stmtLabel i) $ braces s
   
guardStmt :: Int -> Doc 
guardStmt i
  = stmtCounter i <+> text ">" <+> int 0 <+> text "->"
    
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
              -> SetMap
              -> (M.Map Int [Int])
              -> Pid 
              -> Stmt Int 
              -> Doc
renderStmtAbs f pm cfg me (SSend p ms i)
  = guardStmt i <+> block (recv : ctrs)
  where
    recv = renderStmtConc f pm me (SSend p [(mt, SSkip i) | (mt,_) <- ms] i)
    ctrs = inOutCounters cfg i
    
renderStmtAbs f pm cfg me (SRecv ms i)
  = guardStmt i <+>
    ifs ( text "skip" : [ render1 (mt, SSkip i) oc | ((mt,_), oc) <- outms] )
  where
    outms = assert (length ms == length outcs) $ zip ms outcs
    outcs = outCounters cfg i
    render1 m oc = recvGuard f me [m] <+> text "->" <$>
                      block ((renderStmtConc f pm me $ SRecv [m] i) : [decrCounter i, oc])
                            
renderStmtAbs _ _ cfg _ (SVar _ i)
  = guardStmt i <+>
    block (inOutCounters cfg i)
       
renderStmtAbs _ _ _ _ (SSkip _)
  = text "skip"
   
renderStmtAbs _ _ cfg _ (SLoop _ _ i)
  = guardStmt i <+>
    block (inOutCounters cfg i)
    -- where 
    --   isVar :: Stmt Int -> Bool
    --   isVar (SVar v' _) = v == v'
    --   isVar _           = False
    --   vs = [ j | (SVar _ j) <- listify isVar ss ]

renderStmtAbs _ _ _ _ s
  = text $ "assert(0 == 1) /* TBD:" ++ show s
   
nonDetSkip :: Int -> Doc 
nonDetSkip i
  = labelStmt i $
    ifs [ stmtCounter i <+> text ">" <+> int 0 <+> text "->" <+> text "skip"
        , gotoStmt (i + 1)
        ]

stmtCounter :: Int -> Doc
stmtCounter i
  = text "stmt_count_" <> int i
    
decrCounter :: Int -> Doc
decrCounter i
  = text "__DEC" <> parens (stmtCounter i)

incrCounter :: Int -> Doc
incrCounter i
  = text "__INC" <> parens (stmtCounter i)
    
gotoStmt :: Int -> Doc
gotoStmt i
  = text "goto" <+> stmtLabel i

recvGuard :: ChanMap -> Pid -> [(MType, a)] -> Doc
recvGuard f me ms
  = (hcat $ punctuate (text "||") (map go ms))
  where
    go (m, _) = text "nempty" <> parens (f me m)

renderProcStmts :: ChanMap -> SetMap -> Process a -> Doc
renderProcStmts f m (p, s) 
  = vcat [ text "int" <+> text v <> semi | (V v) <- recvVars vs ] <$> 
    cvs <$>
    if isAbs p then 
      label (text "end") $
        doLoop $ 
          map (atomic . return . renderStmt f m p) $ listify notSkip ss
    else
      renderStmt f m p ss
  where
    notSkip (SSkip _)       = False
    notSkip _               = True
    recvVars                = filter (not . isProcVar p) . nub
    isProcVar (PAbs v _) v'    = v == v'
    isProcVar (PUnfold v _ _) v' = v == v'
    isProcVar _          _  = False
    ss                      = freshIds s
    vs                      = listify go ss :: [Var]
    go :: Var -> Bool
    go                      = const True
    cs                      = foldl max 0 ss :: Int
    cvs                     = if isAbs p then
                                vcat [ text "int" <+> 
                                       stmtCounter c <> 
                                       semi | c <- [1..cs+1] ] <$>
                                stmtCounter 1 <+> equals <+> text "__K__" <> semi
                              else
                                empty
  
renderProc :: ChanMap -> SetMap -> Process a -> Doc
renderProc f m p
  = text "proctype" <+>
           renderProcTypeName (fst p) <+>
           renderProcTypeArgs (fst p) <$>
           block [ renderProcStmts f m p ]

renderProcs :: Config a -> SetMap -> Doc
renderProcs (Config { cTypes = ts, cProcs = ps }) m
  = foldl' (\d p -> d <$$> render1 p) empty psfilter
  where
    render1 = renderProc (switchboard $ length ts) m
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
    declAbsVars = [ text "int" <+> text v | PAbs (V v) _ <- map fst ps ]
    boardInits  = do p <- filter (not . isUnfold . fst) ps
                     t <- ts
                     return $ initSwitchboard (length ts) (fst p) t
    procInits   = map (runProc m . fst) ps
    pidInits    = map ((\p -> renderProcVar p (sz p)) . fst) ps
    sz p        = maybe (err p) id $ M.lookup p m
    err p       = error ("Unknown pid (renderMain): " ++ show p)

runProc :: PidMap -> Pid -> Doc
runProc _ p@(PConc _) 
  = text "run" <+> 
    renderProcTypeName p <>
    parens empty

runProc m p@(PAbs (V v) (S s) )
  = text "run" <+> renderProcTypeName p <> parens (int i)
  where
    (i, _) = maybe err id $ M.lookup p m
    err     = error ("Unknown pid (runProc): " ++ show p)
              
runProc m p@(PUnfold _ _ i)
  = text "run" <+> renderProcTypeName p <> parens (int (v + i))
    where
    (v, _) = maybe err id $ M.lookup p m
    err    = error ("Unknown pid (runProc): " ++ show p)

renderProcVar :: Pid -> (Int, Int) -> Doc                  
renderProcVar (PConc x) (i, _)
  = (renderProcName (PConc x)) <+> equals <+> (int i)
renderProcVar (PAbs _ (S s)) (i, sz)
  = seqStmts $ map (uncurry go) (zip [0..setSize-1] (repeat i) ++
                                 zip [setSize..sz-1] [(i+1)..(i+sz-setSize)])
  where
    go j k = text s <> brackets (int j) <+> equals <+> int k
renderProcVar p@(PUnfold _ _ i) (v, _)
  = unfoldProcVar p <+> equals <+> int (v + i)

unfoldProcVar :: Pid -> Doc
unfoldProcVar p@(PUnfold _ _ i)
  = renderProcPrefix p <> text "Unfold_" <> int i

declProcVar :: Pid -> (Int, Int) ->  Doc             
declProcVar p@(PConc _) _
  = renderProcDecl (renderProcName p) <> semi
declProcVar p@(PAbs (V _) (S _)) (_, sz)
  = renderProcDecl (renderProcPrefix  p) <> brackets (int sz) <> semi
declProcVar p@(PUnfold (V _) (S _) i) (_, sz)
  = renderProcDecl (unfoldProcVar p) <> semi 
             
declProcVars :: PidMap -> Doc
declProcVars m
  = M.foldrWithKey go empty m
  where
    go pid k d = declProcVar pid k <$> d
                 
declChannels :: PidMap -> [MType] -> Doc
declChannels pm ts 
  = vcat $ map (\t -> vcat $ map (go t) (M.keys pm)) ts
  where
    go t p@(PConc _)  = text "chan" <+> renderChanName p t
                               <+> equals
                               <+> text "[1] of"
                               <+> encloseSep lbrace rbrace comma
                                     (text "mtype" : map (const (text "int")) (tyargs t))
                                     <> semi
    go t p@(PAbs _ _) = text "chan" <+> renderChanName p t <> brackets (int (sz p))
                               <+> equals
                               <+> text "[1] of"
                               <+> encloseSep lbrace rbrace comma
                                     (text "mtype" : map (const (text "int")) (tyargs t))
                                     <> semi
    go _ (PUnfold _ _ _)= empty
    sz p                = maybe (err p) snd $ M.lookup p pm
    err p               = error ("Unknown pid (runProc): " ++ show p)

buildPidMap :: Config a -> PidMap
buildPidMap (Config { cUnfold = us, cProcs = ps })
  = fst $ foldl go (foldl go (M.empty, 0) (snd pids)) (fst pids)
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
{-
(5, 4)
5 
5 
6 
7 
-}
declSwitchboard :: PidMap -> [MType] -> Doc
declSwitchboard pm ts
  = renderSwitchboard nprocs (length ts)
    where 
      nprocs = M.foldrWithKey (\p v s -> s + count p v) 0 pm
      count (PAbs _ _) (_, n) = n - setSize + 1
      count (PConc _) (_,n) = n
      count _ _          = 0
  
render :: Show a => Config a -> Doc
render c@(Config { cTypes = ts })
  = mtype
    <$$> text "#define __K__" <+> int infty
    <$$> text "#define __INC(_x) _x = (_x < __K__ -> _x + 1 : _x)"
    <$$> text "#define __DEC(_x) _x = (_x < __K__ -> _x - 1 : _x)"
    <$$> declProcVars pidMap
    <$$> declChannels pidMap ts
    <$$> declSwitchboard pidMap ts
    <$$> procs
    <$$> renderMain pidMap unfolded
  where
    unfolded                 = unfold c
    pidMap                   = buildPidMap unfolded
    mtype                    = renderMTypes ts
    procs                    = renderProcs unfolded setMap
    setMap                   = M.foldrWithKey goKey M.empty pidMap
    goKey (PAbs _ s) (_,n) m = M.insert s n m
    goKey _          _     m = m
