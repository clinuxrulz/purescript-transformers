-- | This module defines the CPS monad transformer.

module Control.Monad.Cont.Trans
  ( ContT(..), runContT, mapContT, withContT
  , module Control.Monad.Trans
  , module Control.Monad.Cont.Class
  ) where

import Prelude

import Control.Monad.Trans (MonadTrans, lift)
import Control.Monad.Eff.Class (MonadEff, liftEff)
import Control.Monad.Cont.Class
import Control.Monad.Reader.Class (MonadReader, ask, local)
import Control.Monad.State.Class (MonadState, state)
import Control.Monad.Rec.Class (MonadRec, tailRecM)
import Data.Either (Either(Left, Right), either)

-- | The CPS monad transformer.
-- |
-- | This monad transformer extends the base monad with the operation `callCC`.
newtype ContT r m a = ContT ((a -> m r) -> m r)

-- | Run a computation in the `ContT` monad, by providing a continuation.
runContT :: forall r m a. ContT r m a -> (a -> m r) -> m r
runContT (ContT f) k = f k

-- | Modify the underlying action in a `ContT` monad action.
mapContT :: forall r m a. (m r -> m r) -> ContT r m a -> ContT r m a
mapContT f m = ContT (\k -> f $ runContT m k)

-- | Modify the continuation in a `ContT` monad action
withContT :: forall r m a b. ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b
withContT f m = ContT (\k -> (runContT m) (f k))

instance monadContContT :: (Monad m) => MonadCont (ContT r m) where
  callCC f = ContT (\k -> runContT (f (\a -> ContT (\_ -> k a))) k)

instance functorContT :: (Monad m) => Functor (ContT r m) where
  map f m = ContT (\k -> runContT m (\a -> k $ f a))

instance applyContT :: (Monad m) => Apply (ContT r m) where
  apply f v = ContT (\k -> runContT f $ (\g -> runContT v (\a -> (k $ g a))))

instance applicativeContT :: (Monad m) => Applicative (ContT r m) where
  pure a = ContT (\k -> k a)

instance bindContT :: (Monad m) => Bind (ContT r m) where
  bind m k = ContT (\k' -> runContT m (\a -> runContT (k a) k'))

instance monadContT :: (Monad m) => Monad (ContT r m)

instance monadTransContT :: MonadTrans (ContT r) where
  lift m = ContT (\k -> m >>= k)

instance monadEffContT :: (MonadEff eff m) => MonadEff eff (ContT r m) where
  liftEff = lift <<< liftEff

instance monadReaderContT :: (MonadReader r1 m) => MonadReader r1 (ContT r m) where
  ask = lift ask
  local f c = ContT \k -> do
    r <- ask
    local f (runContT c (local (const (r :: r1)) <<< k))

instance monadStateContT :: (MonadState s m) => MonadState s (ContT r m) where
  state = lift <<< state

data SuspF a next
  = Suspend (Unit -> next)
  | Done a

newtype SuspT m a = SuspT (m (SuspF a (SuspT m a)))

unSuspT :: forall m a. SuspT m a -> m (SuspF a (SuspT m a))
unSuspT (SuspT a) = a

suspSuspend :: forall m a. (Applicative m) => (Unit -> SuspT m a) -> SuspT m a
suspSuspend thunk = SuspT $ return $ Suspend thunk

newtype SuspContT r m a = SuspContT ((a -> SuspT m r) -> SuspT m r)

unSuspContT :: forall r m a. SuspContT r m a -> ((a -> SuspT m r) -> SuspT m r)
unSuspContT (SuspContT a) = a

runSuspContT :: forall r m a. (MonadRec m) => SuspContT r m a -> (a -> m r) -> m r
runSuspContT (SuspContT c) f = runSuspT $ c (\a -> SuspT $ Done <$> f a)

runSuspT :: forall m r. (MonadRec m) => SuspT m r -> m r
runSuspT (SuspT s) = s >>= (tailRecM go)
  where
    go :: SuspF r (SuspT m r) -> m (Either (SuspF r (SuspT m r)) r)
    go (Suspend thunk) = Left <$> (unSuspT $ thunk unit)
    go (Done r) = return $ Right r

toSuspContT :: forall r m a. (MonadRec m) => ContT r m a -> SuspContT r m a
toSuspContT (ContT c) = SuspContT (\k -> SuspT $ Done <$> c (\a -> runSuspT $ k a))

fromSuspContT :: forall r m a. (MonadRec m) => SuspContT r m a -> ContT r m a
fromSuspContT (SuspContT c) = ContT (\k -> runSuspT $ c (\a -> SuspT $ Done <$> k a))

suspContTPure :: forall r m a. a -> SuspContT r m a
suspContTPure a = SuspContT (\k -> k a)

suspContTBind :: forall r m a b. (Applicative m) => SuspContT r m a -> (a -> SuspContT r m b) -> SuspContT r m b
suspContTBind (SuspContT ca) f = SuspContT (\k -> suspSuspend (\_ -> ca (\a -> (unSuspContT $ f a) k)))

tailRecSuspContT :: forall r m a b. (MonadRec m) => (a -> SuspContT r m (Either a b)) -> a -> SuspContT r m b
tailRecSuspContT go a =
  let go2 = tailRecSuspContT go
  in
  (go a) `suspContTBind` (either go2 suspContTPure)

instance monadRecContT :: (MonadRec m) => MonadRec (ContT r m) where
  tailRecM go a =
    let go2 = (toSuspContT <<< go)
    in
    fromSuspContT (tailRecSuspContT go2 a)
