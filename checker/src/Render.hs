{-# LANGUAGE ScopedTypeVariables #-}
module Render where

import           Prelude hiding (mapM, sequence, foldl)
import           Text.PrettyPrint.Leijen
import           Data.Foldable
import qualified Data.Map as M
import           Data.List (nub)
import           Data.Generics hiding (empty)

import           AST  

-- | Some useful combinators
setSize :: Int
setSize = 2

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
renderProcPrefix (PConc _)      = text "Proc_"
renderProcPrefix (PAbs _ (S s)) = text s
renderProcPrefix (PVar _)       = empty

renderProcName :: Pid -> Doc
renderProcName p@(PConc i)      = renderProcPrefix p <> int i
renderProcName p@(PAbs (V v) _) = renderProcPrefix p <> brackets (text v)
renderProcName p@(PVar (V v))   = renderProcPrefix p <> text v
                           
renderProcTypeName :: Pid -> Doc     
renderProcTypeName p@(PConc _) = renderProcName p <> text "_Process"
renderProcTypeName p@(PAbs _ _) = renderProcPrefix p <> text "_Process"

renderProcTypeArgs :: Pid -> Doc
renderProcTypeArgs (PConc _) = parens empty
renderProcTypeArgs (PAbs (V v) _) = parens (text "int" <+> text v)

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
    <+> semi
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

-- | Emit Promela code for each statement    
renderStmt :: (Pid -> MType -> Doc) -> Pid -> Stmt Int -> Doc
renderStmt f (p @ (PConc _)) s = renderStmtConc f p s
renderStmt f p s               = renderStmtAbs f p s
-- renderStmt f p s               = nonDetStmts $ map (renderStmtAbs f p) ss
--   where
--     ss = listify (\(_::Stmt Int) -> True) s
        
sendMsg :: (Pid -> MType -> Doc) -> Pid -> MType -> Doc 
sendMsg f p m
  = f p m <> text "!" <> renderMsg m

recvMsg :: (Pid -> MType -> Doc) -> Pid -> MType -> Doc 
recvMsg f p m
  = f p m <> text "?" <> renderMsg m
                   
renderStmtConc :: (Pid -> MType -> Doc) -> Pid -> Stmt Int -> Doc
renderStmtConc f me (SSend p [(m,s)] _)
  = align (sendMsg f p m <> semi <$>
           renderStmt f me s)
renderStmtConc f me (SSend p ms _)
  = ifs $ map go ms
  where 
    go (m, s) = 
      text "::"  <+>
      case s of
        SSkip _ -> 
          sendMsg f p m
        _       ->
          block [ sendMsg f p m, renderStmt f me s ]
      
renderStmtConc f me (SRecv [(m,s)] _)
  = align (recvMsg f me m <> semi <$>
           renderStmt f me s)
renderStmtConc f me (SRecv ms _)
  = text "if"
      $$ vcat (map go ms)
    <$> text "fi"
  where 
    go (m, s) = 
      text "::" <+> 
      case s of 
        SSkip _ -> recvMsg f me m
        _       -> seqStmts [recvMsg f me m, renderStmt f me s]
          
renderStmtConc _ _ (SSkip _)
  = text "skip"
    
renderStmtConc f me (SIter (V v) (S s) ss _)
  = text "int" <+> text ("__" ++ v) <> semi <$>
    forLoop (text ("__" ++ v) <+> text "in" <+> text s)
            (text v <+> equals <+> renderProcName (PAbs (V ("__" ++ v)) (S s)) <> semi <$>
             renderStmt f me ss)
        
renderStmtConc f me (SLoop (V v) ss _)
  = text v <> text ":" <$> renderStmt f me ss
     
renderStmtConc _ _ (SVar (V v) _)
  = text "goto" <+> text v 
    
renderStmtConc f me (SChoose (V v) s ss _)
  = block [ text "select" <+> 
            parens (text v <+> text ":" <+> int 0 <+> text ".." <+> 
                                   int (setSize-1))
          , renderProcName (PVar (V v)) <+> equals <+> renderProcName (PAbs (V v) s)
          , renderStmt f me ss
          ]
    
renderStmtConc f me (SBlock ss _)
  = block $ map (renderStmt f me) ss
          
renderStmtConc _ _ _
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

renderStmtAbs :: (Pid -> MType -> Doc) -> Pid -> Stmt Int -> Doc
renderStmtAbs f me (SSend p ms i)
  = guardStmt i <+> 
    block [ renderStmtConc f me $ SSend p [(mt, SSkip i) | (mt,_) <- ms] i
          , decrCounter i
          , incrCounter (succ i)
          ]
    
renderStmtAbs f me (SRecv ms i)
  = guardStmt i <+>
    ifs ( text "skip" : [ render1 (mt, SSkip i) | (mt,_) <- ms] )
  where
    render1 m = recvGuard f me [m] <+> text "->" <$>
                block [ renderStmtConc f me $ SRecv [m] i
                      , decrCounter i
                      , incrCounter (succ i)                                                    
                      ]
           
renderStmtAbs _ _ (SSkip _)
  = text "skip"
   
renderStmtAbs _ _ (SLoop v ss i)
  = (nonDetStmts $ map (\j -> guardStmt j <+> gotoStmt j) vs) <$>
    block [ decrCounter i
          , incrCounter (succ i)
          ]
    where 
      isVar :: Stmt Int -> Bool
      isVar (SVar v' _) = v == v'
      isVar _           = False
      vs = [ j | (SVar _ j) <- listify isVar ss ]

renderStmtAbs _ _ s
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

recvGuard :: (Pid -> MType -> Doc) -> Pid -> [(MType, a)] -> Doc
recvGuard f me ms
  = (hcat $ punctuate (text "||") (map go ms))
  where
    go (m, _) = text "nempty" <> parens (f me m)

renderProcStmts :: (Pid -> MType -> Doc) -> Process a -> Doc
renderProcStmts f (p, s) 
  = vcat [ text "int" <+> text v <> semi | (V v) <- recvVars vs ] <$> 
    cvs <$>
    if isAbs p then 
      label (text "end") $
        doLoop $ 
          map (renderStmt f p) $ listify notSkip ss
    else
      renderStmt f p ss
  where
    notSkip (SSkip _)       = False
    notSkip _               = True
    recvVars                = filter (not . isProcVar p) . nub
    isProcVar (PAbs v _) v' = v == v'
    isProcVar _          _  = False
    isAbs (PAbs _ _)        = True
    isAbs _                 = False
    ss                      = freshIds s
    vs                      = listify go ss :: [Var]
    go :: Var -> Bool
    go                      = const True
    cs                      = foldl max 0 ss :: Int
    cvs                     = if isAbs p then
                                vcat [ text "int" <+> 
                                       stmtCounter c <> 
                                       semi | c <- [1..cs+1] ]
                              else
                                empty

renderProc :: (Pid -> MType -> Doc) -> Process a -> Doc
renderProc f p
  = text "proctype" <+>
           renderProcTypeName (fst p) <+>
           renderProcTypeArgs (fst p) <$>
           block [ renderProcStmts f p ]

renderProcs :: Config a -> Doc
renderProcs (Config { cTypes = ts, cProcs = ps })
  = foldl' (\d -> (d <$$>) . renderProc (switchboard (length ts)) ) empty ps
    
renderMain :: M.Map Pid Int -> Config a -> Doc
renderMain _ (Config { cTypes = ts, cProcs = ps})
  = text "init" <+> block body
  where
    body              = declAbsVars ++
                        [ atomic pidInits
                        , atomic boardInits
                        , atomic procInits
                        ]
    declAbsVars       = [ text "int" <+> text v | PAbs (V v) _ <- map fst ps ]
    boardInits        = do p <- ps
                           t <- ts
                           return $ initSwitchboard (length ts) (fst p) t
    procInits = map (runProc . fst) ps
    pidInits  = fst $ foldl' (\(d,i) p -> 
                                (renderProcVar p i : d, i + sz p)) 
                             ([], 0) (map fst ps)
    sz (PConc _) = 1
    sz (PAbs _ _) = setSize
                        

runProc :: Pid -> Doc
runProc p@(PConc _) 
  = text "run" <+> 
    renderProcTypeName p <>
    parens empty

runProc p@(PAbs (V v) (S s) )
  = forLoop (text v <+> text "in" <+> text s) 
      (text "run" <+>
       renderProcTypeName p <>
       parens (text v))

renderProcVar :: Pid -> Int -> Doc                  
renderProcVar (PConc x) i
  = (renderProcName (PConc x)) <+> equals <+> (int i)
renderProcVar (PAbs _ (S s)) i
  = seqStmts (map (uncurry go) (zip [0..setSize-1] [i..]))
  where
    go j k = text s <> brackets (int j) <+> equals <+> int k

declProcVar :: Pid -> Doc             
declProcVar p@(PConc _)
  = renderProcDecl (renderProcName p) <> semi
declProcVar p@(PAbs (V _) (S _))
  = renderProcDecl (renderProcPrefix  p) <> brackets (int setSize) <> semi
             
declProcVars :: M.Map Pid Int -> Doc
declProcVars m
  = M.foldrWithKey go empty m
  where
    go pid _ d = declProcVar pid <$> d
                 

declChannels :: M.Map Pid Int -> [MType] -> Doc
declChannels pm ts 
  = vcat $ map (\t -> vcat $ map (go t) (M.keys pm)) ts
  where
    go t p@(PConc _) = text "chan" <+> renderChanName p t
                               <+> equals
                               <+> text "[1] of"
                               <+> encloseSep lbrace rbrace comma
                                     (text "mtype" : map (const (text "int")) (tyargs t))
                                     <> semi
    go t p@(PAbs _ _) = text "chan" <+> renderChanName p t <> brackets (int setSize)
                               <+> equals
                               <+> text "[1] of"
                               <+> encloseSep lbrace rbrace comma
                                     (text "mtype" : map (const (text "int")) (tyargs t))
                                     <> semi


buildPidMap :: [Pid] -> M.Map Pid Int
buildPidMap ps
  = fst $ foldl go (M.empty, 0) ps 
  where 
    go (m, i) p@(PConc _) = (M.insert p i m, succ i)
    go (m, i) p@(PAbs _ _) = (M.insert p i m, i + setSize)
                             
declSwitchboard :: M.Map Pid Int -> [MType] -> Doc
declSwitchboard pm ts
  = renderSwitchboard nprocs (length ts)
    where nprocs = 
            M.foldrWithKey (\p _ s -> s + count p) 0 pm
          count (PConc _)  = 1
          count (PAbs _ _) = setSize
  
render :: Show a => Config a -> Doc
render c@(Config { cTypes = ts, cProcs = ps })
  = mtype
    <$$> (text "#define __K__" <+> int setSize)
    <$$> (text "#define __INC(_x) _x = (_x < __K__ -> _x + 1 : _x)")
    <$$> (text "#define __DEC(_x) _x = (_x < __K__ -> _x - 1 : _x)")
    <$$> declProcVars pidMap
    <$$> declChannels pidMap ts
    <$$> declSwitchboard pidMap ts
    <$$> procs
    <$$> renderMain pidMap c
  where
    pidMap   = buildPidMap (map fst ps)
    mtype    = renderMTypes ts
    procs    = renderProcs c
