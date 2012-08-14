


signature PWB_LOG =
sig

  (* write logName message *)
  val write      : string -> string -> unit
  val pushLogger : string -> (string -> unit) -> unit
  val popLogger  : string -> (string -> unit) option

  val pushLoggerStdOut : string -> unit
  val pushLoggerStdErr : string -> unit
end;


structure PwbOpenHashMap :
sig
  type 'a hash

  val make : unit -> 'a hash
  val member : string -> 'a hash -> bool
  val get : string -> 'a hash -> 'a option
  val update : string -> 'a -> 'a hash -> unit
  val remove : string -> 'a hash -> unit

  val fromList : (string * 'a) list -> 'a hash

  (*val keys : 'a hash -> string list*)

end =
struct
  type 'a hash = ((string * 'a) list) array

  val buckets = 10

  fun hashFunc k =
    (foldr (op +) 0 (map Char.ord (String.explode k))) mod buckets

  fun make () = Array.array (buckets, [])

  fun getBucket k hash =
  let
    val h = hashFunc k
  in
    (h, Array.sub (hash, h))
  end

  fun get k hash =
    case List.find (fn (k',_) => k = k') (#2(getBucket k hash)) of
         NONE => NONE
       | SOME (_,v) => SOME v

  fun member k hash =
    case get k hash of
         NONE => false
       | SOME _ => true


  fun update k v hash =
  let
    fun updateBucket [] = [(k,v)]
      | updateBucket ((k',v')::ls) =
      if k = k'
        then (k,v)::ls
        else (k',v')::(updateBucket ls)

    val (h,l) = getBucket k hash
  in
    Array.update (hash, h, updateBucket l)
  end

  fun remove k hash =
  let
    val (h,l) = getBucket k hash

    fun rm k [] = []
      | rm k ((k',v')::ls) =
      if k = k'
        then ls
        else (k',v')::(rm k ls)
  in
    Array.update (hash, h, rm k l)
  end


  fun fromList' [] hash = hash
    | fromList' ((k,v)::kvs) hash = fromList' kvs (update k v hash; hash)

  fun fromList kvs = fromList' kvs (make ())

end;


structure PwbLog : PWB_LOG   =
struct
  structure M = PwbOpenHashMap

  type loggers = ((string -> unit) list) M.hash

  val loggers : loggers = M.make ()

  fun logger log = M.get log loggers

  fun pushLogger log w =
    M.update log (case M.get log loggers of
                       NONE => [w]
                     | SOME logs => (w::logs)) loggers

  fun popLogger log =
  let
    val l = logger log
    val _ = M.update log (case l of
                               NONE => []
                             | SOME [] => []
                             | SOME (l::logs) => logs) loggers
  in
    case l of
         NONE => NONE | SOME [] => NONE
       | SOME (l::_) => SOME l
  end


  fun write log msg =
    case logger log of
         NONE => ()
       | SOME [] => ()
       | SOME (l::logs) => l msg

  fun compileOutMsg log msg = log ^ ": " ^ msg ^ "\n"

  fun pushLoggerStd log strm =
    pushLogger log (fn x => TextIO.output (strm, compileOutMsg log x))

  fun pushLoggerStdOut log = pushLoggerStd log TextIO.stdOut
  fun pushLoggerStdErr log = pushLoggerStd log TextIO.stdErr

end;

