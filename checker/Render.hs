module Render where

import           Prelude hiding (mapM, sequence, foldl, foldl')
import           Text.PrettyPrint.Leijen
import           Control.Monad.State     hiding (mapM, sequence)
import           Data.Maybe
import           Data.Traversable
import           Data.Foldable
import qualified Data.IntMap as M

import           AST  

x $$ y = align (x <$> y)
atomic :: [Doc] -> Doc
atomic ss = text "atomic" <+> braces (nest 2 $ (linebreak <> seqStmts ss))
block ds = braces (indent 2 $ seqStmts ds)
          
renderProcName (PConc i)  = text ("Proc_" ++ show i)
renderProcName (PAbs (V v) (S s)) = text ("AbsProcs_" ++ v ++ "_in_" ++ s)
renderProcName (PVar (V v))   = text ("Proc_" ++ v)
                                
renderProcTypeName p = renderProcName p <> text "_Process"

renderMType = text . untycon . tycon
renderPids  :: MType -> [Doc]
renderPids
  = map renderProcName . tyargs
              
renderMsg m 
  = hcat $ punctuate comma (renderMType m : renderPids m)

renderMTypes ts
  = text "mtype" 
    <+> equals
    <+> encloseSep lbrace rbrace comma rts
    <+> semi
  where
    rts = map renderMType ts
                            
renderChanName p t 
  = renderProcName p <> text "_" <> renderMType t
    
renderChannels ts ps
  = foldl (\d t -> d <$> channelsForType ps t) empty ts
  where
    channelsForType ps t = foldl (\d p -> d <$> channelForType t p) empty ps
    channelForType t p = text "chan"
                     <+> renderChanName p t
                     <+> equals
                     <+> text "[1]" <+> text "of"
                     <+> encloseSep lbrace rbrace comma
                           (text "mtype" : map (const (text "short")) (tyargs t))
                     <+> semi

data RenderState = RS { counter :: Int
                      , switch  :: Pid -> MType -> Doc
                      , nextStmt :: M.IntMap Int
                      }

initRS = RS { counter = 0
            , switch = const (const empty)
            , nextStmt = M.empty
            }
         
freshInt :: State RenderState Int
freshInt = do modify (\s -> s { counter = counter s + 1 })
              fmap counter get


freshVar :: Doc -> State RenderState Doc
freshVar x = do n <- freshInt
                return (x <> text "__" <> int n)
                       
countVar n = text "__count__" <> int n
                                        
renderShortDecl n
  = text "short" <+> n

renderShortAssn n rhs 
  = renderShortDecl n <+> equals <+> rhs
    
renderStmt :: Pid -> Stmt Int -> State RenderState Doc
renderStmt (p @ (PConc _)) s = renderStmtConc p s
renderStmt p s               = renderStmtAbs p s
                              
guardStmt _ (SSend p m a)
  = countVar a <+> text ">" <+> int 0  <+> text "->"

guardStmt me (SRecv m a)
  =     countVar a <+> text ">" <+> int 0 
    <+> text "&&" <+> text "nempty" <> parens (renderChanName me m) 
    <+> text "->"
                               
renderStmtAbs :: Pid -> Stmt Int -> State RenderState Doc
renderStmtAbs me s@(SSend p m a)
  = do d <- renderStmtConc me s
       return $ atomic [guardStmt me s <$> seqStmts [d]]

renderStmtAbs me s@(SRecv m a)
  = do d <- renderStmtConc me s
       return $ atomic [guardStmt me s <$> seqStmts [d]]
    
renderStmtConc :: Pid -> Stmt Int -> State RenderState Doc
renderStmtConc me (SSend p m a)
  = do send <- fmap switch get
       return (send p m <> text "!" <> renderMsg m)

renderStmtConc me (SRecv m a)
  = do send <- fmap switch get
       return $ seqStmts (go m ++
                            [send me m <> text "?" <> renderMsg m])
  where 
    go :: MType -> [Doc]
    go m = map (renderShortDecl . renderProcName) (tyargs m)
          
renderStmtConc _ s
  = return $ (text "assert(0 == 1) /* TBD:" <+> text (show s) <+> text "*/")
    
renderProcStmtsNonDet p ss
  = do ss' <- mapM (renderStmtAbs p) ss
       return (text "do" 
               $$ (vcat $ map (text "::" <+>) ss')
               $$ text "od")

renderProcStmts :: Process Int -> State RenderState Doc
renderProcStmts (PConc p, ss)
  = fmap seqStmts $ mapM (renderStmt (PConc p)) ss

renderProcStmts pr
  = do ss' <- mapM sequence (fmap (fmap (const freshInt)) (snd pr)) 
       let ids  = fold $ (map (reverse . foldl' (flip (:)) [])) ss'
           m    = foldl (\m (i,j) -> M.insert i j m) M.empty $ zip ids (tail ids)
       modify (\s -> s { nextStmt = m })
       ss'' <- renderProcStmtsNonDet (fst pr) ss'
       return (seqStmts (map (renderShortDecl . countVar) ids 
                        ++ [countVar (head ids) <+> equals <+> int 1, ss'']))
  where
    go = undefined

renderProc :: Process Int -> State RenderState Doc
renderProc p
  = do pr <- renderProcStmts p
       return (text "proctype" 
                  <+> renderProcTypeName (fst p)
                  <+> parens empty 
                  <$> block [pr])

renderProcs :: Config Int -> Doc
renderProcs (ts, ps)
  = flip evalState i $ 
      foldM (\d p -> do { d' <- renderProc p; return (d <$$> d')}) empty ps
    where
      i = initRS { switch = switchboard (length ts)
                 }
    
renderSwitchboard :: Int -> Int -> Doc
renderSwitchboard m n = text "chan" <+> text "switchboard" 
                                    <+> brackets (int (m * n))
                                    <+> semi
                                        
seqStmts = (<> linebreak).  vcat . punctuate semi
             
switchboard :: Int -> Pid -> MType -> Doc 
switchboard np p m = 
  text "switchboard" <+> brackets (
                          (renderProcName p <> text "*" <> int np)
                          <+> text "+"
                          <+> parens (renderMType m <> text "-" <> int 1)
                         )
renderMain :: Config a -> Doc
renderMain (ts, ps) 
  = text "init" <+> block body
  where
    body            = [initSwitchboard, initProcs]
    initSwitchboard = atomic boardInits
    boardInits      = do p <- ps
                         t <- ts
                         return $ switchboard (length ps) (fst p) t 
                                    <+> equals
                                    <+> renderChanName (fst p) t
    initProcs       = text "atomic" <+> braces (seqStmts procInits)
    procInits       = map (runProc . fst) ps
    runProc p       =   text "run" 
                    <+> renderProcTypeName p 
                    <+> parens empty

renderProcVar :: Show a => (Int, Process a) -> Doc                  
renderProcVar (i, p) 
  =  renderShortAssn (renderProcName (fst p)) (int i) <+> semi
                   
renderProcVars :: Show a => [Process a] -> Doc 
renderProcVars = seqStmts . map renderProcVar . zip [0..]
  
render :: Config Int -> Doc
render (ts, ps)
  = mtype <$$> channels 
          <$$> procs
          <$$> renderMain (ts, ps)
  where
    mtype    = renderMTypes ts
    channels = renderChannels ts (map fst ps) 
            <$>renderProcVars ps
            <$>renderSwitchboard (length ts) (length ps)
    procs    = renderProcs (ts, ps)

---

mPing v = MTApp (MTyCon "Ping") [v]
mPong v = MTApp (MTyCon "Pong") [v]
          
tpid1 = PConc 1
tpid2 = PAbs (V "p") (S "ps")
          
test = 
  ([mPing (PVar (V "x")), mPong (PVar (V "x"))]
  , [(tpid2, [SSend tpid1 (mPing tpid2) 0
                             ,SRecv (mPong (PVar (V "x"))) 0])
    ,(tpid1, [SRecv (mPing (PVar (V "x"))) 0
               ,SSend (PVar (V "x")) (mPong tpid1) 0])]) :: Config Int
