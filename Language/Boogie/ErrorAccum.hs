-- | This monad transformer adds the ability to accumulate errors from several ErrorT computations
-- and report them all at once.
module Language.Boogie.ErrorAccum where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Error

-- | Error accumulator: 
-- used in combination with ErrorT to store intermediate computation results, 
-- when errors should be accumulated rather than reported immediately  
newtype ErrorAccumT e m a = ErrorAccumT { runErrorAccumT :: m ([e], a) }

instance (ErrorList e, Monad m) => Monad (ErrorAccumT e m) where
  -- | Attach an empty list of errors to a succesful computation
  return x  = ErrorAccumT $ return ([], x)
  -- | The bind strategy is to concatenate error lists
  m >>= k   = ErrorAccumT $ do
    (errs, res) <- runErrorAccumT m
    (errs', res') <- runErrorAccumT $ k res
    return (errs ++ errs', res')
    
instance ErrorList e => MonadTrans (ErrorAccumT e) where
  lift m = ErrorAccumT $ do
    a <- m
    return ([], a)  
    
-- | Transform an error computation and default value into an error accumlator
accum :: (ErrorList e, Monad m) => ErrorT [e] m a -> a -> ErrorAccumT e m a
accum c def = ErrorAccumT (errToAccum def `liftM` runErrorT c)
  where
    errToAccum def (Left errs)  = (errs, def)
    errToAccum def (Right x)    = ([], x)
        
-- | Transform a typing accumlator back into a regular typing  
report :: (ErrorList e, Monad m) => ErrorAccumT e m a -> ErrorT [e] m a
report accum = ErrorT (accumToErr `liftM` runErrorAccumT accum)
  where
    accumToErr ([], x) = Right x
    accumToErr (es, _) = Left es  

-- | 'mapAccum' @f def nodes@ :
-- Apply type checking @f@ to all @nodes@,
-- accumulating errors from all @nodes@ and reporting them at the end
mapAccum :: (ErrorList e, Monad m) => (a -> ErrorT [e] m b) -> b -> [a] -> ErrorT [e] m [b]
mapAccum f def nodes = report $ mapM (acc f) nodes  
  where
    acc f x  = accum (f x) def
   
-- | 'mapAccumA_' @f nodes@ :
-- Apply type checking @f@ to all @nodes@ throwing away the result,
-- accumulating errors from all @nodes@
mapAccumA_ :: (ErrorList e, Monad m) => (a -> ErrorT [e] m ()) -> [a] -> ErrorAccumT e m ()
mapAccumA_ f nodes = mapM_ (acc f) nodes  
  where
    acc f x  = accum (f x) ()
    
-- | Same as 'mapAccumA_', but reporting the error at the end
mapAccum_ :: (ErrorList e, Monad m) => (a -> ErrorT [e] m ()) -> [a] -> ErrorT [e] m ()
mapAccum_ f nodes = report $ mapAccumA_ f nodes  

-- | 'zipWithAccum_' @f xs ys@ :
-- Apply type checking @f@ to all @xs@ and @ys@ throwing away the result,
-- accumulating errors from all nodes and reporting them at the end
zipWithAccum_ :: (ErrorList e, Monad m) => (a -> b -> ErrorT [e] m ()) -> [a] -> [b] -> ErrorT [e] m ()
zipWithAccum_ f xs ys = report $ zipWithM_ (acc f) xs ys  
  where
    acc f x y  = accum (f x y) ()
