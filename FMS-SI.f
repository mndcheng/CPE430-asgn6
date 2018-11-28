\ requires search order to include message-wid
\ This is done automatically.


\ This software is free for use and modification by anyone for any purpose
\ with no restrictions or source identification of any kind.

\ May 8 2017 Douglas B. Hoffman
\ dhoffman888@gmail.com

[defined] >M4TH [if]
ONLY FORTH DEFINITIONS
>M4TH
 traceoff debug off
anew --fms--
[then]

here
decimal

true constant fmsCheck? \ use false *only* after all classes and their use are fully debugged

[undefined] cell [if] 1 cells constant cell [then]
get-current value dflt-cur
0 value self
0 value ^class

0 [if]
DFA = Data Field Address , Size of object in bytes not including any indexed instance variables
SFA = Superclass Field Address , Superclass
WIDA = WordlistID Address , Wordlist for this class
IFA = Instance Variable Field Address , Last node of linked list for embedded object instance variables
XFA = Indexed Field Address , Width in bytes of indexed elements, if any
[then]

: dfa  ( class -- addr ) [ 1 cells ] literal + ;
: sfa  ( class -- addr ) [ 2 cells ] literal + ;
: wida ( class -- addr ) [ 3 cells ] literal + ;
: ifa  ( class -- addr ) [ 4 cells ] literal + ; 
: xfa  ( class -- addr ) [ 5 cells ] literal + ;

6 cells constant classSize

[undefined] -cell [if]
   -1 cells constant -cell [then]
[undefined] cell- [if]
: cell- ( addr -- addr-cell ) -cell + ; [then]

: >class  ( obj -- class )  \ get the class of an object
  @ cell- @ ;

\ support for indexed objects
\ Set a class and its subclasses to indexed
: <indexed  ( width -- )   ^class xfa !  ;

: (idxBase) ( addr1 -- addr2 ) dup >class dfa @ + ;  

: idxBase  ( -- addr )  \ get base address of idx data area, will be addr of 1st elem
                        \ which is one cell after the limit ( #elems )
  self (idxBase) cell+ ;

: limit ( -- #elems ) self (idxBase) @ ;

: width    ( -- width )  \ width in bytes of an indexed element
  self >class xfa @ ;

fmsCheck? [if]
  : ?idx ( idx -- idx )
    dup 0 limit within 0= abort" ^elem index out of range" ;
    
  : ^elem ( idx -- elem-addr ) ?idx width * idxBase + ;

[else]
  : ^elem ( idx -- elem-addr ) width * idxBase + ;
[then]


\ ***** heap table accessing
\ the heap table is a temporary table that only exists during the
\ definition of a new class.  At the end of the class definition the
\ contents of the heap table are combined with the superclass table
\ to construct the final dispatch table that is allotted in the dictionary.
\ The table will be trimmed of all cells containing zero that are also
\ located at the very end of the table.

0 value hptr  \ will be an allocated pointer
0 value hptrSz \ size in bytes
: hset ( n ptr ior -- ) throw to hptr to hptrSz ;
: initHtbl ( n -- ) cells dup allocate hset  hptr hptrSz erase ;
: HtblSz ( -- #cells ) hptrSz cell / ;
: rszHtbl ( n -- ) cells dup hptr swap resize hset ;
: ^helem ( #cells -- a ) cells hptr + ;
: Stbl ( -- ^dispatch ) ^class sfa @ @ ;
: StblSz ( -- #cells ) Stbl @ cell / ;
: toDtbl ( n #cells -- ) cells ^class @ + ! ;
: buildDtbl
  HtblSz 1 do i ^helem @ dup 0= if i StblSz 1+ < if drop
  i cells Stbl + @ then then i toDtbl loop hptrSz cell - 0 toDtbl ; 

create meta classSize allot  meta classSize erase  here 0 , meta !
      cell meta dfa ! \ for all objects, the first cell contains the dispatch table address 
  here 0 , meta sfa !
 
: cls>wlorder ( class -- )
  >r  get-order begin 
  r@ wida @ swap 1+ r> sfa @ >r r@ meta = until r> drop set-order ;

: <super ( "<superclassName>" -- )
  here dup >r to ^class classSize allot ' >body dup
  r@ classSize move r@ sfa ! wordlist r@ wida ! r> cls>wlorder
  StblSz 1+ initHtbl ^class wida @ set-current ;

: ex-meth ( obj xt -- ) self >r      \ preserve the contents of self
                        swap to self \ set self to the new current object
                        execute      \ execute the method
                        r> to self ; \ restore self to its prior contents

0 value table-offset 

\ We use message-wid wordlist to record and identify all messages during class creation. 
\ But the message definition used for actual message sends will be in the dflt-cur
\ wordlist. This way we can always identify message names that may conflict with
\ other definitions.
wordlist constant message-wid  
get-order message-wid swap 1+ set-order \ make it the first wordlist to be searched, always

: ?isSel ( "<name>" -- table-offset t | f) 
                 \ selector-ID = table-offset
  >in @ bl word count message-wid search-wordlist
  if ( in xt ) drop >in ! bl word find drop >body ( addr ) @ true exit 
  then >in ! false ;


\ For a dispatch table selector, the selector-ID is a table offset.
\ The offset is stored in the body of the selector definition.
\ The address of the offset is subsequently retrieved by obtaining the body address 
\ of the selector's xt.

fmsCheck? [if] 
: not-understood? ( flag -- ) abort" message not understood" ;
: >xt ( table-offset ^dispatch -- xt )
  2dup @ > not-understood? + @ dup 0= not-understood? ;
[else]
: >xt ( table-offset ^dispatch -- xt ) + @ ;
[then]


: make-selector ( "<messageName>" -- )
  ?isSel if drop exit then
  \ not a selector, so create a new one
  get-current
  message-wid set-current \ message definition belongs in message-wid wordlist
  create table-offset cell+ dup to table-offset , set-current  
  does> ( ^obj addr) @ ( ^obj table-offset ) over @ ( ^obj table-offset ^dispatch ) 
  >xt ex-meth ;

: get-selector ( "<messageName>" -- table-offset ) \ table-offset = selector
  ?isSel if ( table-offset ) 
         else \ <messageName> is not a selector, so make it one
           make-selector table-offset 
         then ;

: super ( "<messageName>" -- )
  ?isSel if   
            Stbl >xt compile,
         else 
           true abort" SUPER not followed by a message" 
         then ; immediate

: eself ( "<messageName>" -- ) \ force early bind to self 
  ?isSel if  \ followed by message name, so early bind to it
            dup hptr + @ ?dup if nip else Stbl >xt then
            compile,
         else 
           true abort" ESELF not followed by a message" 
         then ; immediate


\ early bind a message to an object
\ or send a message to an object as if the object were a different class
: class_as> ( obj "<className>" "<messageName>" -- )
  ' >body ?isSel
          if
            swap ( offset cls ) @ >xt
            state @ if ( compiling) postpone literal postpone ex-meth
                    else ex-meth
                    then
          else
           true abort" CLASS_AS> <className> not followed by a message"
          then
  ; immediate


: link ( addr -- ) here over @ , swap ! ;

: lowerCase? ( char -- flag ) \ flag is true if char is lower case
  [char] a [ char z 1+ ] literal within ;

[undefined] bounds [if] : bounds ( addr len -- addr+len addr ) over + swap ; [then]

\ Converts lower-case characters to upper case, modifying the contents
\ starting at addr for cnt chars
: to-upper   ( addr cnt -- )
 bounds \ cnt+addr addr
 ?do i c@ dup lowercase?
  if 32 - i c!
  else drop
  then
 loop ;

: move$ ( src$ptr\dest$ptr --) \ copy src to dest, dest must be long enough
  over c@ 1+ move ;

: do-scan ( $ptr -- $ptr ) \ always converts to upper case
  dup >in @ bl word rot move$ >in ! 
  dup count to-upper ;

: :m ( "<messageName>" -- #table-cells xt )
  get-selector cell / :noname ;

: ;m ( #table-cells xt --)
  postpone ; swap 
  ( xt #table-cells )
    begin
      HtblSz 1- over <
    while
      HtblSz 1+ rszHtbl
      0 HtblSz 1- ^helem ! \ if necessary pad the dispatch table with zeros
    repeat ^helem dup @ abort" Cannot redefine a method in the same class"
    ! \ store the xt at the proper offset in the dispatch table
  ; immediate


\ =====================================================================
\ An instance variable record consists of 4 or 5 cell-sized fields.
\
\   cell    field
\  Offset   Name      Description
\  ------   ----      ---------------------------------------
\    0      link      addr points to link of prior embedded-obj ivar in chain, if any
\    1      class     pointer to class of embedded-obj or -1 if not an embedded-object (i.e. just an ivar)
\    2      offset    offset in owning object to this embedded-obj or ivar
\    3      name      32-bit hash value of embedded-obj or ivar name
\    4      #elems    maximum number of elements available in an indexed eo 
\                        (this last cell is only present for indexed classes of eos)
\ =====================================================================


\ **** instance variable primitives ****
 
: hash-ivar  ( addr len -- hash ) \ from Dick Pountain JFAR Vol3 Number 3 p68
  32 min 0 swap 0 do over i + c@ i 1+ * + loop swap drop ;

: check-hash-collision  ( ivarname-hash addr -- )
  begin dup @
  while dup @ 3 cells + @ over
            =  \ compare hash
            if abort" ivar name or name hash collision, choose another name" then
            @ 
  repeat 2drop ;

: hash>  ( "name" -- hash )  bl word count hash-ivar
  ^class if dup ^class ifa check-hash-collision then ;

: ((bytes)) ( n id "name" -- offset )
  align ^class ifa link  \ store link
   ( id) , \ mark this as a normal ivar or as an embedded-object
  ^class dfa @ ( n) ,  \ store offset to ivar
  >in @ hash> , >in ! ; \ store hashed ivar name
\ **** end instance variable primitives ****


\ ****** ivar words ********
: setup-ivar ( offset "name" -- ) create immediate ( offset ) , ;
 
: ivar-action \ compile time: ( addr -- )
              \ run time: ( -- ivar-addr )
  @ ( offset ) postpone self
  \ optimize for offset = 0
  ?dup IF postpone literal postpone + THEN ;

: make-ivar ( offset "name" -- )
  setup-ivar does> ivar-action ;

: (bytes) ( n "name" -- offset )
   -1 ((bytes))
  ^class dfa dup @ ;

: bytes ( n "name" -- )
  (bytes) make-ivar +! ;

\ an ivar will have size of cell bytes
: ivar ( "name" -- ) cell bytes ; \ a convenience
\ ****** end ivar words ********


\ ****** ivalue words ********
: make-ival ( offset "name" -- )
  setup-ivar does> ivar-action postpone @ ;

\ ivalue will have a size of cell bytes
: ivalue ( "name" -- ) cell (bytes) make-ival +! ; 

: to-iv ( n "ivarname" -- ) \ only works in a definition, works for ivalues and ivars (but prefer @ and ! for ivars)
  ' >body @ ( offset ) postpone literal postpone self postpone + postpone ! ; immediate
\ ****** end ivalue words ********


\ ****** embedded-object words ********

: ?execute-method-eo ( addr -- ) 
    \ input stream:    ( "<message:>" -- )  early bind message send to ivar
    \     or        ( "<non-message>" -- ^obj ) just leave addr of embedded-object 
          >r
          postpone self r@ @ ( offs ) ?dup if postpone literal postpone + then
          ?issel
          if \ early bind to following message
          ( addr )
            ( table-offset ) r@ cell+ @ @ ( ^dspatch ) >xt ( xt )
            postpone literal postpone ex-meth
          then r> drop ;

: embed-make-ivar ( ^cls-eo offset "eo-name" --)
  create immediate ( n ) , ( ^cls-eo ) ,
  does> ?execute-method-eo ;

: embed-bytes ( ^cls-eo n "eo-name" --)
  >r ^class dfa dup >r @ embed-make-ivar r> r> swap ( n dfa ) +! ;

: embed-obj ( ^cls-eo "eo-name" | #elems ^cls-eo "eo-name" -- )
  dup ((bytes))
  dup >r xfa @ dup
    if \ this is an indexed class
    ( #elems width ) over , \ store #elems in linked-list node
    * cell+  \ cell+ allows for #elems at start of idxBase
    then
  r@ dfa @ + ( size-of-eo ) r> swap embed-bytes ;  
\ ****** end embedded-object words ********

0 value (dict)-xt \ will contain xt for (dict)

: ?execute-method
  state @
  if
    ?isSel
    if
    \ early bind to following message
    ( addr sel-type )
      ( obj table-offset ) over @ rot postpone literal ( obj table-offset ^dspatch ) >xt 
      postpone literal postpone ex-meth
    else \ no message so just compile addr of object
      postpone literal
    then
  then ;

: (obj) \ Compile time ( "spaces<name>" -- ) \ name of the new dictionary object
   create  immediate
   \ Run time: ( -- ^obj )
   \   or execute: ^obj <message:>
   does> ?execute-method ; 

: build ( class | #elems class -- )
  ^class
  if embed-obj \ inside a class definition, so we are building an embedded object as ivar declaration
  else \ outside a class definition, so instantiate a new named dictionary object
    (obj)
    (dict)-xt execute drop
  then ;

0 value saved-order 

: save-order 
  get-order
  dup 1+ cells allocate throw to saved-order
  ( widn ... wid1 n )
  dup saved-order ! \ store n in first cell of allocated pointer
  1+ 1 do saved-order i cells + ! loop ; \ store wids


\ a word to restore the search order and current wordlist
variable cnt
: restore 
  saved-order 0= if exit then
  saved-order @ cnt !
  begin
   saved-order cnt @ cells + @
   -1 cnt +! cnt @
  while \ while cnt <> 0
  repeat
  saved-order @ set-order  saved-order free throw
  0 to saved-order
  dflt-cur set-current ;

\ Have restore execute when a method compilation error occurs, such
\ as encountering an undefined word. This will be Forth system specific.
\ The following is what I use with MacForth on VFX:
 
[defined] >M4TH [if]
' restore is BeforeAlert 
[then]


: scanForSuper
  pad do-scan ( dup ) count s" <SUPER" compare  \ $ptr flag
  if s" <SUPER OBJECT" evaluate then ;  

: :class ( "name" -- ) \ name of the new class being defined
   get-current to dflt-cur
   save-order create immediate
   scanForSuper
   does> build ;  

: classalign  ( -- )  \ align class data size (optional)
	^class dfa @  aligned  ^class dfa ! ;

: ;class   
  restore
  classalign
  ^class , \ store class one cell before dispatch table 
   here ^class ! \ ^class must contain ^dispatch
   hptrSz allot
  buildDtbl  hptr free throw
  0 to ^class ;

\ create these two messages now 
make-selector init:
make-selector free: 


\ The total memory for all eos, both indexed and non-indexed,
\ will already have been allotted/allocated at this time.
\ What remains to be done is to store ^dispatch values,
\ and store the #elems (indexed eos only)

: init-eos ( obj class -- ) 
    ifa
  begin \ walk the linked-list
    @ ?dup
  while
    ( we may have an eo )
    >r
       r@ cell+ @ -1 <>  \ if class field is -1, then this is an ivar, not an eo
       if \ we have an eo
	       r@ [ 2 cells ] literal + @ ( obj eo-offset )
	       over + ( obj eo )
	       r@ cell+ @ ( obj eo ^class-eo )
	       2dup @ swap ( obj eo ^class-eo ^dispatch eo ) ! \ store ^dispatch
	       ( obj eo ^class-eo )
	       dup xfa @
	         if
	            \ this is an indexed eo
	            r@ [ 4 cells ] literal + @ ( obj eo ^class-eo #elems )
	            >r 2dup ( obj eo ^class-eo eo ^class-eo )
	            dfa @ ( obj eo ^class-eo eo indexed-offset-eo ) +
	                  ( obj eo ^class-eo indexed-addr-eo )            
	            r> swap ( obj eo ^class-eo #elems indexed-addr-eo ) !  \ store #elems in eo
	            ( obj eo ^class-eo )
	         then
	       ( obj eo ^class-eo ) over >r
	       recurse \ must set up eos of eos nested to any level
	       r> drop
       then
    r>
  repeat  drop ;

: deep_init ( obj -- )
  dup >class ( obj class ) init-eos  ;

: (allot) ( cls n -- cls addr )
  align here ( cls n addr ) swap ( cls addr n ) allot ;

\ to allow optional use of regions
defer allocate'  
defer free' 
defer newsize' 
defer throw'

: region-reset ; \ place holder definition

\ use newsize in place of resize where you want the option of using region
\ but notice the difference in parameter input
: newsize ( n-new old-ptr n-old -- ptr ior )
  drop swap resize ;

: region-off
  ['] allocate is allocate'
  ['] free     is free'
  ['] newsize  is newsize'
  ['] throw    is throw'
  ;
region-off


: (allocate) ( cls n -- cls addr )
  allocate' throw' ;

: (make-nonindexed) ( xt cls n -- obj )
  rot execute ( cls obj )
  swap ( obj cls ) @ ( obj ^disp )
  over    ( obj ^disp obj ) ! ; \ store ^dispatch in cell 1

: make-nonindexed ( cls xt -- obj )
  swap \ xt cls
  dup dfa @ ( xt cls n )
  (make-nonindexed) ;

: make-indexed ( #elems cls xt width -- obj )
  >r rot >r \ cls xt  r: width #elems
  swap \ xt cls
  dup dfa @ \ xt cls n0
  2r@ * + \ xt cls n 
  cell+
  (make-nonindexed) \ obj
  dup >class dfa @ over + \ obj obj+n
  r> swap  ( obj #elems obj+n ) ! \ store #elems
  r> drop ;

: make-obj ( cls xt | #elems cls xt -- obj )
  over xfa @ ?dup
  if   \ an indexed class
   make-indexed
  else \ not an indexed class
   make-nonindexed
  then dup deep_init dup >r init: r> ;

: (dict) ( cls | #elems cls -- obj )
  ['] (allot) make-obj ;
' (dict) to (dict)-xt

: (heap) ( cls | #elems cls -- obj )
  ['] (allocate) make-obj ;


:class object <super meta
 :m init: ;m 
 :m free: ;m 
;class

\ heap> can be used at interpretation and run time 
: heap>   ( "spaces<classname>" -- obj )
  ' >body state @
  if
    postpone literal  postpone (heap)
  else
    (heap)
  then ; immediate

\ dict> can be used at interpretation and run time 
: dict>   ( "spaces<classname>" -- obj )
  ' >body state @
  if
    postpone literal  postpone (dict)
  else
    (dict)
  then ; immediate

: <free  ( obj --) dup free: free' throw' ;


: (is-kindOf) ( object-class target-class -- flag )
  swap
  begin
    2dup = if 2drop true exit then
    sfa @ dup ['] object >body = if 2drop false exit then
  again ;


\ obj must be exactly = classname 
: is-a ( obj "classname" -- flag ) 
  state @
  if   postpone >class ' >body postpone literal postpone =
  else >class ' >body =
  then ; immediate


\ obj may be a subclass of classname, or = classname
: is-kindOf ( obj "classname" -- flag ) 
  state @
  if   postpone >class ' >body postpone literal postpone (is-kindOf)
  else >class ' >body (is-kindOf)
  then ; immediate

cr here swap - . .(  bytes used) \ 11570 VFX

-1 [if]
\ ------- begin optional DotParse code
 
: find-ivar-offset  ( ivarname-hash addr -- ivar-offset true | false ) 
  begin @ dup
  while 2dup 3 cells + @ = if  2 cells + @ ( offset )  nip true  exit then
  repeat nip ;

: find-ivar  ( ^obj ivarname-hash ^class -- ivar-addr | ival-contents ) 
   ifa find-ivar-offset 
   if ( ^obj ivar-offset ) + \ ivar-addr or eo-addr
   else
     true abort" ivar name not found"
   then ;

\ interpret only, cannot be compiled
: iv ( ^obj "name" -- ivar-addr ) \ input stream: "spaces<ivarname>"
    dup >class \ ^obj ^class
    hash> ( ^obj ^class ivarname-hash )
    swap find-ivar ;

\ compile only
: [iv] ( ^obj "name" -- ivar-addr )
  postpone dup postpone >class ( ^obj ^class )
  hash> postpone literal  ( ^obj ^class ivarname-hash )
  postpone swap postpone find-ivar ; immediate

: add$ ( src$ptr\dest$ptr --) \ adds src$ to the end of dest$.  src$ is unchanged.
  >r count tuck r@ count + swap cmove
  r@ c@ + r> c! ;

create parsed$ 128 allot 

: (convert-source$) ( $ptr -- )
  0 parsed$ c!
  pad ( source$) count bounds 
  ?do i c@ [char] . =
      if dup parsed$ add$
      else i c@ parsed$ count + c!
            parsed$ c@ 1+ parsed$ c!
      then
  loop drop ;

: convert-source$ 
\   replace all "."  with " iv " or " [iv] "
  state @
  if
    c"  [iv] " 
  else
    c"  iv " 
  then  (convert-source$) ;

: dotParse 
     convert-source$  parsed$ count EVALUATE ;

\ ANS compatible
: .. ( -- addr ) \ addr of ivar or embedded-object 
    \ Input (typical): .. MyLine.p1.y0  \ leaves address of object y0 or ivar y0 if an ivar
    
    \ or ( ^obj -- )
    \ Input stream (typical): .. .p1.y0
  bl word ( src )  pad ( source$) ( dest ) move$
  dotParse ; immediate

\ ------- end DotParse code
[then]

-1 [if] \ Optional introspection.  Test if an object can respond to a given message.

: >xt' ( table-offset ^dispatch -- xt | 0 )
  2dup @ > if 2drop false exit then
  + @ ;

: (has-meth) ( obj addr -- xt | 0 )
  swap @ >xt' ;
  

\ return non-zero (actually the method xt) if the object will respond to the method, otherwise return false
: has-meth ( obj "messageName" -- xt | 0 ) \ can use ex-meth on xt to execute the method 
  ' >body @ state @
  if   postpone literal postpone (has-meth)
  else (has-meth)
  then ; immediate


\ given the class name return the class
: class ( "classname" -- ^class )
  ' >body state @
  if postpone literal then ; immediate

[then]




0 [if] \ Optional Diagnostics/Inspection code 

\ see file "FMS-SI Object and Class Structure.pdf" for a detailed explanation
\ of the class information dump provided by the following utility.
\ Example Use:  dc string  \ 'dump class' string

: (dd) ( ^cls -- )
  ." DISPATCH TABLE"
  to ^class 
  cr ." address " ." cell#  " ." XT  " 
  cr ^class @ cell - . -1 . ^class >class . ."  => ^class at cell -1"
  ^class @ @  cell /  1+ 0
  ?DO cr ^class @ i cells + . i . ^class @ i cells + @ .
   i 0= if ."  cell 0 contains the max valid table-offset" then
  LOOP cr ;

: (dump-ivars) ( addr -- )
  cr ."   eo-class   offset-in-object(bytes)  name-hash   elemWidth   #elems" cr
  begin
    @ ?dup
  while
    >r
       r@ cell+ @ dup -1 = swap 0= or
       if \ this is an ivar or ivalue
         r@ cell+ @ ( -1 ) 2 spaces .  r@ 2 cells + @ ( offset ) ( 2 pick +) 8 spaces . 
         r@ 3 cells + @ ( name-hash ) 23 spaces u. cr
       else \ an embedded-object 
         r@ cell+ @ ( -1 ) 2 spaces .  r@ 2 cells + @ ( offset ) 2 pick + 8 spaces . 
         r@ 3 cells + @ ( name-hash ) 23 spaces u.
         r@ cell+ @ ( ^class-eo ) xfa @ ?dup if 22 spaces .  8 spaces  r@ 4 cells + @ ( #elems ) . then cr
       then
    r>
  repeat ;

0 value addr 
: (dc) ( ^class -- )
  cr ." DUMP CLASS"
 0 to addr to ^class 
 cr ^class . 2 spaces 0 . ." ^class=" ^class . ." ^class @ => " ^class @ .  ." = ^dispatchTable"
 cr  ^class DFA dup . 2 spaces 1  . @  . ."  ^class DFA @  => obj length without indexed area"
 cr  ^class SFA dup . space 2  . @ . ."   ^class SFA @ => superclass "
 cr  ^class WIDA dup . space 3  . @ . ."   ^class WIDA @ => wordlist id "
 cr  ^class IFA dup . space 4  . @ . ."   ^class IFA @ => ^ifa "
 cr  ^class XFA dup . space 5  . @ . ."   ^class XFA @ => width "
 ^class IFA cr ." IVARS" (dump-ivars)
 ;

\ "dump class"
: dc  \ usage: dc <classname>  
 ' >body
 to ^class 
 ^class (dc)
 ^class (dd)
 0 to ^class ;

0 value addr'
: d \ { n addr  -- } \ for debugging, addr = beginning address n = # of cells to dump
  to addr'
  0 ?DO CR I . addr' I CELLS + DUP . @ . LOOP ;
 
[then]


