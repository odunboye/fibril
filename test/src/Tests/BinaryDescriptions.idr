module Tests.BinaryDescriptions

import Data.Fin
import Data.IORef
import Data.List
import Fibril.Data.Bytes
import Fibril.Core.Term
import Fibril.Core.Quantity
import Fibril.Core.Context
import Fibril.Core.Runtime
import Fibril.Core.Reduction
import Fibril.Core.WeakHead
import Fibril.Core.EffectAdmission
import Fibril.Core.ResourceAdmission
import Fibril.Driver.Binary
import Fibril.Effect.Console
import Fibril.Effect.ConsoleProgram
import Fibril.Driver.Console
import Fibril.Driver.Interactive
import Fibril.Driver.Native.Emit
import Fibril.Driver.Resource
import Fibril.Runtime.Binary
import Fibril.Runtime.ScopedInput

%default total

accepted : Term 0 -> Term 0 -> Bool
accepted term ty = case checkRuntime 512 128 Empty term ty of
  Left _ => False
  Right _ => True

public export
echo : Nat -> Term 0
echo size = IOBind byteReadResultType UnitType (ReadBytes (naturalTerm size))
  (Lambda Linear byteReadResultType
    (VariantCase (Lambda Erased byteReadResultType (IOType UnitType)) (Variable FZ)
      [IOPure UnitValue, Lambda Linear BytesType (WriteBytes (Variable FZ))]))

rejected : Either a b -> Bool
rejected (Left _) = True
rejected _ = False

hidden : Term 0
hidden = BoolCase BoolFalse (echo 1) (IOPure UnitValue)

-- Every example is raw syntax; scan erased annotations before type checking.
wrappers : List (Term 0)
wrappers = [RejectBytes, FlushBytes, ReadBytes NatZero, WriteBytes (BytesValue empty), hidden,
  Lambda Erased FlushBytes UnitValue, Pi Erased FlushBytes UnitType,
  Sigma Erased Erased FlushBytes UnitType,
  NominalType "x" [FlushBytes] UnitType,
  VariantType [Just (Erased, FlushBytes)],
  RecFold FlushBytes UnitValue UnitValue UnitValue,
  SeqFold UnitValue UnitValue FlushBytes UnitValue,
  UTF8Encode FlushBytes, BytesSlice NatZero FlushBytes (BytesValue empty)]

public export
checks : List (String, Bool)
checks =
  [("binary rejection is inert IO Unit", accepted RejectBytes (IOType UnitType)),
   ("binary rejection remains an explicit capability", rejected (prepareIO 128 128 RejectBytes) && rejected (prepareInteractive 128 128 RejectBytes)),
   ("binary read is typed inert IO", accepted (ReadBytes (naturalTerm 2)) (IOType byteReadResultType)),
   ("binary write requires Bytes", not (accepted (WriteBytes (StringValue "x")) (IOType UnitType))),
   ("binary flush is typed IO Unit", accepted FlushBytes (IOType UnitType)),
   ("binary read capacity requires Nat", not (accepted (ReadBytes UnitValue) (IOType byteReadResultType))),
   ("binary echo checks independently", accepted (echo 2) (IOType UnitType)),
   ("full normalization leaves binary requests inert", case normalize 0 (the (Term 0) FlushBytes) of Normal FlushBytes => True; _ => False),
   ("head normalization leaves binary requests inert", case weakHead 0 (the (Term 0) FlushBytes) of HeadForm FlushBytes => True; _ => False),
   ("all admission wrapper positions are scanned", all containsBinaryRequest wrappers),
   ("binary runner rejects hidden text requests", rejected (prepareBinary (BoolCase BoolFalse (WriteLine (StringValue "hidden")) (IOPure UnitValue)))) ,
   ("binary runner rejects raw file references", rejected (prepareBinary (IOPure (FileHandleValue 1 0)))),
   ("binary argument resource scans remain exhaustive", containsFileReference (the (Term 0) (ReadBytes (FileHandleValue 1 0))) && containsFileReference (the (Term 0) (WriteBytes (FileHandleValue 1 0)))),
   ("output planner rejects dormant binary requests", rejected (prepareIO 128 128 hidden)),
   ("interactive preparation rejects dormant binary requests", rejected (prepareInteractive 128 128 hidden)),
   ("all old C modes reject dormant binary requests", rejected (emitCheckedC hidden) && rejected (emitCheckedInteractiveC 64 8192 hidden) && rejected (emitCheckedResourceC 64 8192 hidden)),
   ("explicit binary C mode accepts binary descriptions", not (rejected (emitCheckedBinaryC 2 4 (echo 2)))),
   ("binary C mode rejects dormant text", rejected (emitCheckedBinaryC 2 4 (BoolCase BoolFalse (WriteLine (StringValue "hidden")) (IOPure UnitValue)))) ,
   ("binary C admission bounds are explicit", rejected (emitCheckedBinaryC 100001 8 (echo 2)) && rejected (emitCheckedBinaryC 2 8388609 (echo 2))),
   ("pure bytes are not IO capabilities", not (containsBinaryRequest (the (Term 0) (BytesValue (fromList [0,255])))))]

record Facts where
  constructor Observed
  host : BinaryAdapters
  reads : IORef Nat
  writes : IORef (List Bytes)
  flushes : IORef Nat

facts : Either BinaryError (Maybe Bytes) -> Either BinaryError () -> Either BinaryError () -> IO Facts
facts input output final = do
  reads <- newIORef (the Nat 0)
  writes <- newIORef (the (List Bytes) [])
  flushes <- newIORef (the Nat 0)
  let host = BinaryHost
        (\_ => do modifyIORef reads S; pure input)
        (\bytes => do modifyIORef writes (\xs => xs ++ [bytes]); pure output)
        (do modifyIORef flushes S; pure final)
  pure (Observed host reads writes flushes)

succeeded : Either BinaryRunError () -> Bool
succeeded (Right ()) = True
succeeded _ = False

fault : Either BinaryRunError () -> BinaryError -> Bool
fault (Left (BinaryTransportFailure actual)) expected = actual == expected
fault _ _ = False

public export
covering
runBinaryDescriptionChecks : IO (List (String, Bool))
runBinaryDescriptionChecks = do
  let octets = fromList (map cast (the (List Nat) [0..255]))
  good <- facts (Right (Just octets)) (Right ()) (Right ())
  allBytes <- runBinaryTermWith 64 1024 2 512 good.host (echo 256)
  written <- readIORef good.writes
  flushed <- readIORef good.flushes
  let captured = fromList [0,255]
  short <- facts (Right (Just captured)) (Right ()) (Right ())
  shortResult <- runBinaryTermWith 64 128 2 6 short.host (echo 4)
  charged <- facts (Right (Just captured)) (Right ()) (Right ())
  exhausted <- runBinaryTermWith 64 128 2 5 charged.host (echo 4)
  deniedWrites <- readIORef charged.writes
  deniedFlushes <- readIORef charged.flushes
  empty <- facts (Right Nothing) (Right ()) (Right ())
  eof <- runBinaryTermWith 64 128 1 4 empty.host (echo 4)
  eofWrites <- readIORef empty.writes
  faultHost <- facts (Left (BinaryReadFailed captured)) (Right ()) (Right ())
  readFailure <- runBinaryTermWith 64 128 2 8 faultHost.host (echo 4)
  failureWrites <- readIORef faultHost.writes
  failureFlushes <- readIORef faultHost.flushes
  writeHost <- facts (Right (Just captured)) (Left (BinaryWriteFailed 1)) (Right ())
  writeFailure <- runBinaryTermWith 64 128 2 8 writeHost.host (echo 4)
  writeFlushes <- readIORef writeHost.flushes
  finalHost <- facts (Right Nothing) (Right ()) (Left BinaryFlushFailed)
  finalFailure <- runBinaryTermWith 64 128 0 0 finalHost.host (IOPure UnitValue)
  flushing <- facts (Right Nothing) (Right ()) (Right ())
  explicit <- runBinaryTermWith 64 128 1 0 flushing.host FlushBytes
  flushCount <- readIORef flushing.flushes
  zero <- facts (Right Nothing) (Right ()) (Right ())
  zeroResult <- runBinaryTermWith 64 128 1 0 zero.host (echo 0)
  zeroReads <- readIORef zero.reads
  denied <- facts (Right Nothing) (Right ()) (Right ())
  deniedResult <- runBinaryTermWith 64 128 0 0 denied.host (BoolCase BoolFalse (WriteLine (StringValue "bad")) (IOPure UnitValue))
  admissionFlushes <- readIORef denied.flushes
  resource <- runResourceTermWith 64 128 64
    (ResourceHost (\_ => pure (Right ())) (pure (Right Nothing)) (pure (Right ())) (\_, _ => pure ())) hidden
  let resourceRejected = case resource of
        ExecutedResources (Left ResourceAdmission) [] 0 => True
        _ => False
  reduced <- facts (Right Nothing) (Right ()) (Right ())
  reductionError <- runBinaryTermWith 64 0 0 0 reduced.host
    (Apply (Lambda Linear UnitType (IOPure (Variable FZ))) UnitValue)
  reductionFlushes <- readIORef reduced.flushes
  afterWrite <- facts (Right Nothing) (Right ()) (Right ())
  afterWriteError <- runBinaryTermWith 64 0 1 2 afterWrite.host
    (IOBind UnitType UnitType (WriteBytes (BytesValue captured))
      (Lambda Linear UnitType (UnitCase (Variable FZ) (IOPure UnitValue))))
  acceptedBeforeError <- readIORef afterWrite.writes
  afterWriteFlushes <- readIORef afterWrite.flushes
  rejecting <- facts (Right Nothing) (Right ()) (Right ())
  protocolFailure <- runBinaryTermWith 64 128 0 0 rejecting.host RejectBytes
  rejectedReads <- readIORef rejecting.reads
  rejectedWrites <- readIORef rejecting.writes
  rejectedFlushes <- readIORef rejecting.flushes
  let protocolRejected = case protocolFailure of
        Left BinaryRejected => True
        _ => False
  pure
    [("checked hosted binary echo preserves all octets", succeeded allBytes && written == [octets] && flushed == 1),
     ("short read keeps full reservation", succeeded shortResult && fault exhausted BinaryByteLimit && null deniedWrites && deniedFlushes == 0),
     ("EOF is a value and writes nothing", succeeded eof && null eofWrites),
     ("physical read prefix is retained in typed driver failure", fault readFailure (BinaryReadFailed captured) && null failureWrites && failureFlushes == 0),
     ("partial write count is retained without final flush", fault writeFailure (BinaryWriteFailed 1) && writeFlushes == 0),
     ("mandatory final flush is checked without request fuel", fault finalFailure BinaryFlushFailed),
     ("explicit flush spends one request, final flush spends none", succeeded explicit && flushCount == 2),
     ("zero read fails before the adapter", fault zeroResult BinaryZeroRead && zeroReads == 0),
     ("admission failure invokes no final flush", rejected deniedResult && admissionFlushes == 0),
     ("description failure invokes no final flush", rejected reductionError && reductionFlushes == 0),
     ("resource runner rejects binary syntax before creating a session", resourceRejected),
     ("later driver failure does not masquerade as successful flush", rejected afterWriteError && acceptedBeforeError == [captured] && afterWriteFlushes == 0),
     ("protocol rejection performs no transport action or final flush", protocolRejected && rejectedReads == 0 && null rejectedWrites && rejectedFlushes == 0)]
