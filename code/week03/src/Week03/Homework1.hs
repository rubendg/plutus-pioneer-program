{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module Week03.Homework1 where

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (FromJSON, ToJSON)
import           Data.Map             as Map
import           Data.Text            (Text)
import           Data.Void            (Void)
import           GHC.Generics         (Generic)
import           Ledger               hiding (singleton)
import           Ledger.Ada           as Ada
import           Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Playground.Contract  (ToSchema, ensureKnownCurrencies,
                                       printJson, printSchemas, stage)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Plutus.Contract
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (unless)
import           Prelude              (IO)
import qualified Prelude              as P
import           Text.Printf          (printf)

import           Data.Default
import           Ledger.TimeSlot
import           Wallet.Emulator
w1 = pubKeyHash $ walletPubKey $ Wallet 1
w2 = pubKeyHash $ walletPubKey $ Wallet 2

-- note that in the plutus playground the time is / 1000
slot10 = slotToBeginPOSIXTime def 10
slot5 = slotToBeginPOSIXTime def 5
slot6 = slotToBeginPOSIXTime def 6

data VestingDatum = VestingDatum
    { beneficiary1 :: PubKeyHash
    , beneficiary2 :: PubKeyHash
    , deadline     :: POSIXTime
    } deriving (P.Show, ToJSON, Generic)

PlutusTx.unstableMakeIsData ''VestingDatum

{-# INLINABLE mkValidator #-}
-- This should validate if either beneficiary1 has signed the transaction and the current slot is before or at the deadline
-- or if beneficiary2 has signed the transaction and the deadline has passed.
mkValidator :: VestingDatum -> () -> ScriptContext -> Bool
mkValidator (VestingDatum taker giver d) _ ctx =
  traceIfFalse "claiming funds failed" $ cond1 || cond2
  where

  cond1 = isSignedBy taker && beforeDeadline
  cond2 = isSignedBy giver && deadlineReached

  info = scriptContextTxInfo ctx

  isSignedBy = txSignedBy info

  range = txInfoValidRange info

  beforeDeadline = to d `contains` range

  deadlineReached = from (d + 1) `contains` range

data Vesting
instance Scripts.ValidatorTypes Vesting where
    type instance DatumType Vesting = VestingDatum
    type instance RedeemerType Vesting = ()

typedValidator :: Scripts.TypedValidator Vesting
typedValidator = Scripts.mkTypedValidator @Vesting
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @VestingDatum @()

validator :: Validator
validator = Scripts.validatorScript typedValidator

valHash :: Ledger.ValidatorHash
valHash = Scripts.validatorHash typedValidator

scrAddress :: Ledger.Address
scrAddress = scriptAddress validator

data GiveParams = GiveParams
    { gpBeneficiary :: !PubKeyHash
    , gpDeadline    :: !POSIXTime
    , gpAmount      :: !Integer
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type VestingSchema =
            Endpoint "give" GiveParams
        .\/ Endpoint "grab" ()

give :: AsContractError e => GiveParams -> Contract w s e ()
give gp = do
    pkh <- pubKeyHash <$> ownPubKey
    let dat = VestingDatum
                { beneficiary1 = gpBeneficiary gp
                , beneficiary2 = pkh
                , deadline     = gpDeadline gp
                }
        tx  = mustPayToTheScript dat $ Ada.lovelaceValueOf $ gpAmount gp
    ledgerTx <- submitTxConstraints typedValidator tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @P.String $ printf "made a gift of %d lovelace to %s with deadline %s"
        (gpAmount gp)
        (P.show $ gpBeneficiary gp)
        (P.show $ gpDeadline gp)

grab :: forall w s e. AsContractError e => Contract w s e ()
grab = do
    now    <- currentTime
    logInfo @P.String $ printf "now"
    logInfo $ now
    pkh    <- pubKeyHash <$> ownPubKey
    utxos  <- utxoAt scrAddress

    logInfo @P.String "utxos"
    forM_ utxos logInfo

    logInfo @P.String "datums"
    forM_ utxos (\x -> logInfo $ datum x)

    let utxos1 = Map.filter (isSuitable $ \dat -> beneficiary1 dat == pkh && now <= deadline dat) utxos
        utxos2 = Map.filter (isSuitable $ \dat -> beneficiary2 dat == pkh && now >  deadline dat) utxos
    logInfo @P.String $ printf "found %d gift(s) to grab" (Map.size utxos1 P.+ Map.size utxos2)
    unless (Map.null utxos1) $ do
        let orefs   = fst <$> Map.toList utxos1
            lookups = Constraints.unspentOutputs utxos1 P.<>
                      Constraints.otherScript validator
            tx :: TxConstraints Void Void
            tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ PlutusTx.toData () | oref <- orefs] P.<>
                      mustValidateIn (to now)
        void $ submitTxConstraintsWith @Void lookups tx
    unless (Map.null utxos2) $ do
        let orefs   = fst <$> Map.toList utxos2
            lookups = Constraints.unspentOutputs utxos2 P.<>
                      Constraints.otherScript validator
            tx :: TxConstraints Void Void
            tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ PlutusTx.toData () | oref <- orefs] P.<>
                      mustValidateIn (from now)
        void $ submitTxConstraintsWith @Void lookups tx
  where
    datum :: TxOutTx -> Maybe VestingDatum
    datum o = case txOutDatumHash $ txOutTxOut o of
        Nothing -> Nothing
        Just h  -> case Map.lookup h $ txData $ txOutTxTx o of
            Nothing        -> Nothing
            Just (Datum e) -> PlutusTx.fromData e

    isSuitable :: (VestingDatum -> Bool) -> TxOutTx -> Bool
    isSuitable p o = case txOutDatumHash $ txOutTxOut o of
        Nothing -> False
        Just h  -> case Map.lookup h $ txData $ txOutTxTx o of
            Nothing        -> False
            Just (Datum e) -> maybe False p $ PlutusTx.fromData e

endpoints :: Contract () VestingSchema Text ()
endpoints = (give' `select` grab') >> endpoints
  where
    give' = endpoint @"give" >>= give
    grab' = endpoint @"grab" >>  grab

mkSchemaDefinitions ''VestingSchema

mkKnownCurrencies []
