;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;[ARCHIVO SIN TILDES]

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos. Toda instancia del problema es codificada
; por un grafo cuyos vertices determinan las distintas regiones del mapa, y cuyas aristas definen la contiguidad de
; dichas regiones. De manera que, los datos de entrada del sistema seran los elementos (vertices y aristas) del grafo
; correspondiente al mapa sobre el que se desea obtener una respuesta.

;TODO BREVE EXPLICACION DEL MODELO DE COMPUTACION CELULAR CON MEMBRANAS BASADO EN TEJIDOS
;TODO BREVE EXPLICACION DEL SISTEMA IMPLEMENTADO (ESTRUCTURAS DE DATOS, REGLAS, HECHOS, INTERFAZ, USO DE INTERFAZ Y EJEMPLOS PREDEFINIDOS)

;BIBLIOGRAFIA (REFERENCIAS Y DOCUMENTACION)
;REFERENCIAS
;R1. Every planar graph is four colorable - Part1: Discharging
;   [https://projecteuclid.org/euclid.ijm/1256049011]
;R2. Every planar graph is four colorable - Part2: Reducibility
;   [https://projecteuclid.org/euclid.ijm/1256049012]
;R3. Solving 3-COL with Tissue P Systems
;   [http://www.gcn.us.es/4BWMC/vol2/diaz.pdf]
;R4. A uniform family of tP systems with cell division solving 3-COL in a linear time
;   [http://www.sciencedirect.com/science/article/pii/S030439750800251X]

;DOCUMENTACION
;D1.CLIPS Documentation
;   [http://www.clipsrules.net/?q=Documentation]
;D2.CLIPS Basic Reference Guide
;   [https://www.csie.ntu.edu.tw/~sylee/courses/clips/bpg/top.html]
;D3.Conceptos basicos de la computacion celular con membranas
;   [http://www.sema.org.es/ojs/index.php?journal=sema&page=article&op=view&path%5B%5D=191]
;D4.Modelos de computacion celular con membranas
;   [http://www.p-lingua.org/mecosim/matvida/course/Unidad2_Computaci%F3nCelularConMembranas.pdf]
;D5.A CLIPS simulator for Recognizer P Systems with Active Membranes
;   [http://cantor.cs.us.es/2BWMC/bravolpdf/CLIPS.pdf]

;ESTRUCTURAS DE DATOS
(deftemplate membrana "datos que definen una membrana dentro del sistema p"
  (slot etiqueta)
  (slot identificador)
  (slot estado (allowed-values inicializacion division comunicacion))
  (slot configuracion (allowed-values actual siguiente))
  (multislot contenido)

)

(deftemplate regla-division "datos que definen una regla de division para el sistema p"

  ;[elemento-izquierda](etiqueta) -> [elemento1-derecha](etiqueta)[elemento2-derecha](etiqueta)

  (slot etiqueta)
  (multislot elemento-izquierda)
  (multislot elemento1-derecha)
  (multislot elemento2-derecha)

)

(deftemplate regla-comunicacion "datos que definen una regla de comunicacion para el sistema p"

  ;(etiqueta-izquierda, elemento1-izquierda elemento2-izquierda/elemento1-derecha elemento2-derecha, etiqueta-derecha)

  ;Una regla de comunicacion tiene como maximo 4 elementos, 2 maximo por parte de la membrana con etiqueta-izquierda
  ; y otros 2 maximo por parte de la membrana con etiqueta-derecha. Los elementos especificados de cada membrana seran
  ; los intercambiados entre las mismas.

  (slot etiqueta-izquierda)
  (multislot elemento1-izquierda)
  (multislot elemento2-izquierda)
  (slot etiqueta-derecha)
  (multislot elemento1-derecha)
  (multislot elemento2-derecha)

)

(deftemplate envia-elemento "modela el envio de un elemento desde una membrana a otra"
  (slot etiqueta-emisor)
  (slot etiqueta-receptor)
  (multislot elemento-enviado)
  (slot numero-copias)

)

(deftemplate instancia-3col "define una instancia del problema 3-COL a partir del grafo que la codifica"
  (slot n-vertices)
  (multislot vertices) ;(vertices , A 1 , A 2 , ... , An ,)
  (slot m-aristas)
  (multislot aristas)  ;(aristas , A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

)

;FUNCIONES AUXILIARES
(deffunction techo (?valor) "calcula la funcion matematica techo del valor pasado como parametro"
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))

)

;VARIABLES GLOBALES
(defglobal ?*n-vertices* = 0
           ?*m-aristas* = 0
           ?*techo-log2-m* = 0 ;Valor necesario para la generacion de ciertos elelentos en funcion de la instancia del problema.
           ?*id* = 2)          ; Valor de referencia para identificar nuevas membranas.

;REGLAS (INICIALIZACION, DIVISION y COMUNICACION)
;TODO Introducir datos sobre configuraciones, la membrana 0 es mucha tela, hay que buscar discriminantes para las reglas de comunicacion.

;TODO Implementar regla para mostrar el resultado final a partir de la entrada dada. Necesidad de funcion contar elementos x por ejemplo ¿?
;TODO Implementar regla para lanzar interfaz de usuario e introducir instancias del problema manualmente
;TODO Incluir en inicializacion mensajes descriptivos del proceso para determinar cuando empieza el proceso real.
;TODO Incluir mensajes descriptivos a lo largo del proceso de decision.

;INICIALIZACION
(defrule lee-instancia-3-col "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  ;ESTRUCTURA DE MEMBRANAS
  (assert
          ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con datos de una instancia concreta del problema.
          ; Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
          (membrana (etiqueta 0)
                    (identificador entorno)
                    (estado inicializacion)
                    (contenido , b , D , S , N ,)) ;Constantes presentes para cualquier instancia del problema.

          (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
                    (identificador 1)
                    (estado comunicacion)
                    (contenido , a 1 , b , c 1 , yes , no ,))

          ;La membrana 2 contiene, entre otros, los elementos de entrada que representan una instancia del problema,
          ; por tanto tambien requiere ser inicializada.
          (membrana (etiqueta 2)
                    (identificador 2)
                    (estado inicializacion)
                    (contenido , D ,))) ;Constantes presentes para cualquier instancia del problema.


  ;DATOS DE INICIALIZACION
  ;Guarda en variables globales el numero de vertices y aristas, necesarios para la inicializacion del sistema.
  (bind ?*n-vertices* ?n-vertices)
  (bind ?*m-aristas* ?m-aristas)

  ;Guarda en una variable global el valor del techo del logaritmo en base 2 de m, necesario para la inicializacion del sistema.
  (bind ?log2-m (/ (log ?m-aristas) (log 2)))
  (bind ?*techo-log2-m* (techo ?log2-m))


  (assert ;REGLAS DE COMUNICACION (1 <-> 0)
          (regla-comunicacion (etiqueta-izquierda 1)  ;r22
                              (elemento1-izquierda b)
                              (elemento2-izquierda T)
                              (etiqueta-derecha 0)
                              (elemento1-derecha S))

          (regla-comunicacion (etiqueta-izquierda 1) ;r23
                              (elemento1-izquierda S)
                              (elemento2-izquierda yes)
                              (etiqueta-derecha 0))

          (regla-comunicacion (etiqueta-izquierda 1) ;r24
                              (elemento1-izquierda a (+ (* 2 ?*n-vertices*) ?*techo-log2-m* 12))
                              (elemento2-izquierda b)
                              (etiqueta-derecha 0)
                              (elemento1-derecha N))

          (regla-comunicacion (etiqueta-izquierda 1) ;r25
                              (elemento1-izquierda N)
                              (elemento2-izquierda no)
                              (etiqueta-derecha 0)))

  (assert ;REGLAS DE COMUNICACION (2 <-> 0)
          (regla-comunicacion (etiqueta-izquierda 2) ;r6
                              (elemento1-izquierda c (+ (* 2 ?*n-vertices*) 1))
                              (etiqueta-derecha 0)
                              (elemento1-derecha d 1)
                              (elemento2-derecha E))

          (regla-comunicacion (etiqueta-izquierda 2) ;r8
                              (elemento1-izquierda E)
                              (etiqueta-derecha 0)
                              (elemento1-derecha e)
                              (elemento2-derecha f 2))

          (regla-comunicacion (etiqueta-izquierda 2) ;r19
                              (elemento1-izquierda e)
                              (elemento2-izquierda z)
                              (etiqueta-derecha 0))

          (regla-comunicacion (etiqueta-izquierda 2) ;r20
                              (elemento1-izquierda f (+ ?*techo-log2-m* 7))
                              (elemento2-izquierda e)
                              (etiqueta-derecha 0)
                              (elemento1-derecha T))

          ;REGLAS DE COMUNICACION (1 <-> 2)
          (regla-comunicacion (etiqueta-izquierda 1) ;r5
                              (elemento1-izquierda c (+ (* 2 ?*n-vertices*) 1))
                              (etiqueta-derecha 2)
                              (elemento1-derecha D))

          ;REGLAS DE COMUNICACION (2 <-> 1)
          (regla-comunicacion (etiqueta-izquierda 2) ;r21
                              (elemento1-izquierda T)
                              (etiqueta-derecha 1)))

  ;VERTICES Y ARISTAS
  ;Hechos para la inicializacion de vertices y aristas.
  ; (assert (inicializa-vertices ?n-vertices $?vertices) ;(, A 1 , A 2 , ... , A n ,)
  ;         (inicializa-aristas ?m-aristas $?aristas))   ;(, A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

  ;CONTADORES

  ;Hechos para la inicializacion de los distintos tipos de contadores del sistema.
  (assert ;(inicializa-contadores a)
          (inicializa-contadores c))
          ;(inicializa-contadores d)
          ;(inicializa-contadores f))

  ;CONSTANTES
  ;Hecho para la inicializacion de ciertas constantes del sistema.
  ;Para la constantes E, e, T y z, que interactuan con las membranas etiquetadas por 2, es necesario generar 3 elevado a n copias.
  ;(assert (inicializa-constantes))

  ;REGLAS
  ;Hecho para la inicializacion de las reglas del sistema.
  ;Las reglas se generan a patir del numero de vertices y las aristas que definen las instancia del problema 3-COL.
  (assert (inicializa-reglas))

)

(defrule inicializacion-vertices "introduce en el sistema los elementos referentes a los vertices"
  (declare (salience 99)) ;Tiene la prioridad mas alta para que se inicialicen en primer lugar.

  ?iv <- (inicializa-vertices ?pendientes $?vi , A ?i , $?vf)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (estado inicializacion)
                          (contenido $?c0))

  ?membrana2 <- (membrana (etiqueta 2) ;Entrada
                          (estado inicializacion)
                          (contenido $?c2))

  =>
  (retract ?iv)

  ;Genera la lista de elementos referentes al vertice con indice i, para despues insertarla en el entorno.
  ; Ademas, para cada elemento crea 3 elevado a n copias, pues cada elemento asociado a un vertice interactua con cada
  ; membrana etiquetada por 2. De manera que interactua con 3 elevado a n membranas.

  (bind ?vertices (create$ R ?i , B ?i , G ?i ,))
  (bind ?copias (integer (** 3 (- ?*n-vertices* 1)))) ;Indica el numero de copias necesearias de cada elemento.
  (bind ?k 1)

  ;Los elementos Ri, Bi, Gi deben ser copiados 3 elevado a n-1 veces por cada i. Esto se debe a que tras la fase de generacion,
  ; para cada vertice i habra 3 elevado a n-1 celulas con cada posible valor de ese indice. Es decir, habra
  ; 3 elevado a n-1 celulas con Ri para i = 1, 3 elevado a n-1 celulas con Bi para i = 1, etc...
  ;
  ; Esta medida, entre otras, se lleva a cabo para ajustar al maximo el numero de elementos en el entorno, pues de lo contrario
  ;  el proceso se vuelve muy costoso en tiempo por la equiparacion de patrones de CLIPS.
  ;
  ; Por ejemplo, Ai y Ti, no se incluyen en el entorno pues no son necesarios para que se aplique ninguna regla concreta.

  (while (< ?k ?copias)
         (bind ?vertices (insert$ ?vertices 1 R ?i , B ?i , G ?i ,))
         (bind ?k (+ ?k 1)))


  (bind ?copias (* (- ?i 1) (integer (** 3 ?*n-vertices*)))) ; (i - 1)*(3 elevado a n)
  (bind ?vertices (insert$ ?vertices 1 RC ?i , BC ?i , GC ?i ,))
  (bind ?k 1)

  ;El numero de copias necesarias para RC, BC y GC viene determinada por indice y el numero de celulas con etiqueta 2.
  ; Esto se debe a que las aristas cumplen las condicion 1 <= i < j <= n para sus indices, de manera que por ejemplo, no existe
  ; ninguna arista que tenga j = 1, para j = 2 solo puede haber una arista con i = 1, para j = 3 solo puede haber 2 aristas con
  ; i = 1 e i = 2, etc...

  (while (< ?k ?copias)
         (bind ?vertices (insert$ ?vertices 1 RC ?i , BC ?i , GC ?i ,))
         (bind ?k (+ ?k 1)))

  ;Introduce en el entorno los elementos generados de los vertices.
  (modify ?membrana0 (contenido $?c0 ?vertices)) ;Entorno

  ;En la membrana de entrada solo es necesario incluir el vertice correspondiente.
  (modify ?membrana2 (contenido $?c2 A ?i ,))

  ;Comprueba si existen vertices que no han sido procesados.
  (if (neq ?pendientes 1)
    then (assert (inicializa-vertices (- ?pendientes 1) $?vi , $?vf))

    else (assert (vertices))) ;Se han incluido todos los elementos de los vertices en las membranas correspondientes.

)

(defrule inicializacion-aristas "introduce en el sistema los elementos referentes a las aristas"
    (declare (salience 98)) ;Seran inicializadas en segundo lugar.

    ?ia <- (inicializa-aristas ?pendientes $?ai , A ?i ?j , $?af)

    ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                            (estado inicializacion)
                            (contenido $?c0))

    ?membrana2 <- (membrana (etiqueta 2) ;Entrada
                            (estado inicializacion)
                            (contenido $?c2))

  =>
  (retract ?ia)

  ;Genera la lista de elementos referentes a la arista con indices i j para despues insertarla en el entorno.
  ; Ademas, para cada elemento crea 3 elevado a n copias, pues cada elemento asociado a una arista interactua con cada
  ; membrana etiquetada por 2 tras la fase de generacion.

  (bind ?aristas (create$ P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
  (bind ?copias (integer (** 3 ?*n-vertices*)))
  (bind ?k 1)

  (while (< ?k ?copias)
         (bind ?aristas (insert$ ?aristas 1 P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
         (bind ?k (+ ?k 1)))

  ;Introduce en el entorno los elementos generados de las aristas.
  (modify ?membrana0 (contenido $?c0 ?aristas)) ;Entorno

  ;En la membrana de entrada solo es necesario incluir la arista correspondiente.
  (modify ?membrana2 (contenido $?c2 A ?i ?j ,))

  ;Reglas asociadas a las aristas. (2 <-> 0)
  (assert (regla-comunicacion (etiqueta-izquierda 2)  ;r10ij
                              (elemento1-izquierda d (+ ?*techo-log2-m* 1))
                              (elemento2-izquierda A ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha P ?i ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r11ij
                              (elemento1-izquierda P ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha R ?i ?j)
                              (elemento2-derecha PC ?i ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r12ij
                              (elemento1-izquierda PC ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha B ?i ?j)
                              (elemento2-derecha G ?i ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r13ij
                              (elemento1-izquierda R ?i)
                              (elemento2-izquierda R ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha R ?i)
                              (elemento2-derecha RC ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r14ij
                              (elemento1-izquierda B ?i)
                              (elemento2-izquierda B ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha B ?i)
                              (elemento2-derecha BC ?j))

          (regla-comunicacion (etiqueta-izquierda 2) ;r15ij
                              (elemento1-izquierda G ?i)
                              (elemento2-izquierda G ?i ?j)
                              (etiqueta-derecha 0)
                              (elemento1-derecha G ?i)
                              (elemento2-derecha GC ?j)))

  ;Comprueba si hay aristas que no han sido procesadas.
  (if (neq ?pendientes 1)
    then (assert (inicializa-aristas (- ?pendientes 1) $?ai , $?af))

    else (assert (aristas))) ;Se han incluido todos los elementos de las aristas en las membranas correspondientes.

)

(defrule inicializacion-contadores "genera los contadores necesarios en el entorno"
  (declare (salience 97))

  ?ic <- (inicializa-contadores ?tipo)

  ?entorno <- (membrana (etiqueta 0)
                        (estado inicializacion)
                        (contenido $?c0))

  =>
  (retract ?ic)

  (bind ?contadores (create$))
  (switch ?tipo
      (case a ;1 ... 2n + [log2(m)] + 12
        then (bind ?indice-a 1)
             (bind ?limite-a (+ (*  2 ?*n-vertices*) ?*techo-log2-m* 12))
             ;Genera la lista de elementos referentes al contador con indice i para despues insertarla en el entorno.
             ; Ademas, para cada elemento contador crea un numero determinado de copias en funcion de las membranas que
             ; interactuaran con el mismo. En la regla inicial lee-instancia-3-col hay mas informacion al respecto.
             (while (<= ?indice-a ?limite-a)
               ;Para el contador a solo es necesario una copia de cada elemento,
               ; pues unicamente interactua con la membrana etiquetada con 1.
               (bind ?copias-a 1)
               (bind ?k 1)
               (while (<= ?k ?copias-a)
                      (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-a ,))
                      (bind ?k (+ ?k 1)))

               (bind ?indice-a (+ ?indice-a 1)))
        )
      (case c ;1 ... 2n + 1
        then (bind ?indice-c 1)
             (bind ?limite-c (+ (* 2 ?*n-vertices*) 1))
             (while (<= ?indice-c ?limite-c)
               ;Inicialmente, el contador c interactua unicamente con la membrana etiquetada por 1,
               ; pero tras la fase de generacion es necesario disponer de tantas copias del ultimo elemento de c
               ;como membranas con etiqueta 2 se hayan generado. Es decir, 3 elevado a n copias del elemento c con el indice 2n+1.
               (bind ?copias-c (integer (** 2 (- ?indice-c 1))))
               (bind ?k 1)
               (while (<= ?k ?copias-c)
                      (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-c ,))
                      (bind ?k (+ ?k 1)))

               (bind ?indice-c (+ ?indice-c 1)))
        )
      (case d ;1 ... [log2(m)] + 1
        then (bind ?indice-d 1)
             (bind ?limite-d (+ ?*techo-log2-m* 1))
             (while (<= ?indice-d ?limite-d)
               ;Para el contador d, en cada aplicacion de la regla de comunicacion correspondiente, una membrana etiquetada con 2
               ; se trae 2 copias por cada elemento contador d que tiene. De manera que, tras la fase de generacion, al existir
               ; 3 elevado a n membranas etiquetada con 2, es necesario generar 3 elevado a n por 2 elevado a [log2(m)].
               (bind ?copias-d (* (integer (** 2  (- ?indice-d 1)))  ;3 elevado a n por 2 elevado a [log2(m)] copias de d[log2(m)]
                                  (integer (** 3 ?*n-vertices*))))
               (bind ?k 1)
               (while (<= ?k ?copias-d)
                      (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-d ,))
                      (bind ?k (+ ?k 1)))

               (bind ?indice-d (+ ?indice-d 1)))
        )
      (case f ;2 ... [log2(m)] + 7
        then (bind ?indice-f 2)
             (bind ?limite-f (+ ?*techo-log2-m* 7))
             (while (<= ?indice-f ?limite-f)
               ;En el caso del contador f deben generarse 3 elevado a n copias de cada uno, pues estos contadores
               ; interactuan con las membranas con etiqueta 2. Tras la fase de generacion hay 3 elevado a n membranas con etiqueta 2.
               (bind ?copias-f (integer (** 3 ?*n-vertices*)))
               (bind ?k 1)
               (while (<= ?k ?copias-f)
                      (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-f ,))
                      (bind ?k (+ ?k 1)))

               (bind ?indice-f (+ ?indice-f 1)))
        )
      )

  (modify ?entorno (contenido $?c0 ?contadores))
  (assert (contadores ?tipo))

)

(defrule inicializacion-constantes "genera unas lista de constantes necesarias en el entorno"
  (declare (salience 96)) ;Se inicializan en tercer lugar.

  ?ic <- (inicializa-constantes)

  ?membrana0 <- (membrana (etiqueta 0) ;Entorno
                          (estado inicializacion)
                          (contenido $?c0))

  =>
  (retract ?ic)

  ;Genera la lista de los elementos constantes para despues insertarla en el entorno. Para cada elemento
  ; se crean 3 elevado a n copias, pues interactuan con las membranas etiquetadas con 2 tras la fase de generacion.

  (bind ?constantes (create$ E , e , T , z ,))
  (bind ?copias (integer (** 3 ?*n-vertices*)))
  (bind ?k 1)

  (while (< ?k ?copias)
         (bind ?constantes (insert$ ?constantes 1 E , e , T , z ,))
         (bind ?k (+ ?k 1)))

  (modify ?membrana0 (contenido $?c0 ?constantes)) ;Entorno
  (assert (constantes)) ;Se han incluido todas las constantes necesarias.

)

(defrule inicializacion-reglas "genera las reglas del sistema a partir de la instancia del problema 3-COL especificada"
  (declare (salience 95)) ;Se inicializan en ultimo lugar.

  ?ir <- (inicializa-reglas)

  =>
  (retract ?ir)

  ;REGLAS DE COMUNICACION (1 <-> 0)
  (bind ?i 1)
  (while (<= ?i (+ (* 2 ?*n-vertices*) ?*techo-log2-m* 11)) ;i = 1 ... 2n + [log2(m)] + 11

    (assert (regla-comunicacion (etiqueta-izquierda 1) ;r3i
                                (elemento1-izquierda a ?i)
                                (etiqueta-derecha 0)
                                (elemento1-derecha a (+ ?i 1))))

    (if (<= ?i (* 2 ?*n-vertices*)) ;i = 1 ... 2n
      then (assert (regla-comunicacion (etiqueta-izquierda 1) ;r4i
                                       (elemento1-izquierda c ?i)
                                       (etiqueta-derecha 0)
                                       (elemento1-derecha c (+ ?i 1))
                                       (elemento2-derecha c (+ ?i 1)))))

    (if (<= ?i ?*n-vertices*) ;i = 1 ... n
      then (assert
                   ;REGLAS DE DIVISION
                   (regla-division (etiqueta 2) ;r1i
                                   (elemento-izquierda A ?i)
                                   (elemento1-derecha R ?i)
                                   (elemento2-derecha T ?i))

                   (regla-division (etiqueta 2) ;r2i
                                   (elemento-izquierda T ?i)
                                   (elemento1-derecha B ?i)
                                   (elemento2-derecha G ?i))

                  ;REGLAS DE COMUNICACION (2 <-> 0)
                  (regla-comunicacion (etiqueta-izquierda 2) ;r16i
                                      (elemento1-izquierda R ?i)
                                      (elemento2-izquierda RC ?i)
                                      (etiqueta-derecha 0)
                                      (elemento1-derecha z))

                  (regla-comunicacion (etiqueta-izquierda 2) ;r17i
                                      (elemento1-izquierda B ?i)
                                      (elemento2-izquierda BC ?i)
                                      (etiqueta-derecha 0)
                                      (elemento1-derecha z))

                  (regla-comunicacion (etiqueta-izquierda 2) ;r18i
                                      (elemento1-izquierda G ?i)
                                      (elemento2-izquierda GC ?i)
                                      (etiqueta-derecha 0)
                                      (elemento1-derecha z))))

    (if (<= ?i ?*techo-log2-m*) ;i = 1 ... [log2(m)]
      then (assert
                   (regla-comunicacion (etiqueta-izquierda 2) ;r7i
                                       (elemento1-izquierda d ?i)
                                       (etiqueta-derecha 0)
                                       (elemento1-derecha d (+ ?i 1))
                                       (elemento2-derecha d (+ ?i 1)))))

    (if (and (>= ?i 2) (<= ?i (+ ?*techo-log2-m* 6))) ;i = 2 ... [log2(m)] + 6
      then (assert
                    (regla-comunicacion (etiqueta-izquierda 2) ;r9i
                                        (elemento1-izquierda f ?i)
                                        (etiqueta-derecha 0)
                                        (elemento1-derecha f (+ ?i 1)))))

    (bind ?i (+ ?i 1))) ;Incremento para el bucle.

  (assert (reglas)) ;Se han incluido todas las reglas generadas a partir de la instancia del problema.

)

;DIVISION
(defrule division "crea dos nuevas membranas en sustitucion de una existente y a partir de una regla de division concreta"

  (regla-division (etiqueta ?etiqueta) ;Selecciona los elementos que definen la regla de division
                  (elemento-izquierda $?elemento-izquierda)
                  (elemento1-derecha $?elemento1-derecha)
                  (elemento2-derecha $?elemento2-derecha))

  ?membrana <- (membrana (etiqueta ?etiqueta)
                         (estado division)
                         (contenido $?ci , $?elemento-izquierda , $?cf))

  =>
  (retract ?membrana)

  (assert (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 1))
                    (estado division)
                    (contenido $?ci , $?elemento1-derecha , $?cf))

          (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 2))
                    (estado division)
                    (contenido $?ci , $?elemento2-derecha , $?cf)))

  (bind ?*id* (+ ?*id* 2)) ;Incrementa el valor referencia de membranas.

)

;COMUNICACION
(defrule comunicacion "construye los hechos que modelan la comunicacion entre dos membranas a partir una regla de comunicacion concreta"

  (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
                      (elemento1-izquierda $?elemento1-izquierda) ;Siempre hay un valor
                      (elemento2-izquierda $?elemento2-izquierda) ;Puede ser vacio
                      (etiqueta-derecha ?etiqueta-derecha)
                      (elemento1-derecha $?elemento1-derecha)     ;Puede ser vacio
                      (elemento2-derecha $?elemento2-derecha))    ;Puede ser vacio

  (or   ;En este caso la membrana especificada en la parte izquierda de la regla envia 2 elementos. (Antiport)
        (and (membrana (etiqueta ?etiqueta-izquierda)
                       (identificador ?idi)
                       (estado comunicacion)
                       (contenido $? , $?elemento1-izquierda , $?))

             (membrana (etiqueta ?etiqueta-izquierda)
                       (identificador ?idi)
                       (estado comunicacion)
                       (contenido $? , $?elemento2-izquierda , $?)))

        ;En este caso la membrana especificada en la parte izquierda de la regla envia 1 elemento. (Antiport)
        (and (membrana (etiqueta ?etiqueta-izquierda)
                   (estado comunicacion)
                   (contenido $?, $?elemento1-izquierda , $?))

             (test (= (length $?elemento2-izquierda) 0))))

  (or
        ;En este caso la membrana especificada en la parte derecha de la regla envia 2 elementos diferentes. (Antiport)
        (and (membrana (etiqueta ?etiqueta-derecha)
                       (identificador ?idd)
                       (estado comunicacion)
                       (contenido $? , $?elemento1-derecha , $?))

             (membrana (etiqueta ?etiqueta-derecha)
                       (identificador ?idd)
                       (estado comunicacion)
                       (contenido $? , $?elemento2-derecha , $?))

             (test (neq $?elemento1-derecha $?elemento2-derecha)))

        ;En este caso la membrana especificada en la parte derecha de la regla envia 1 elemento. (Antiport)
        (and (membrana (etiqueta ?etiqueta-derecha)
                       (estado comunicacion)
                       (contenido $? , $?elemento1-derecha , $?))

             (test (= (length $?elemento2-derecha) 0)))

        ;En este caso la membrana especificada en la parte derecha de la regla no envia ningun elemento. (Symport)
        (and (test (= (length $?elemento1-derecha) 0))
             (test (= (length $?elemento2-derecha) 0)))

         ;En este caso la membrana especificada en la parte derecha de la regla envia 2 elementos iguales. (Antiport)
         (and  (membrana (etiqueta ?etiqueta-derecha)
                         (estado comunicacion)
                         (contenido $? , $?elemento1-derecha , $?))))

  =>

  (assert (envia-elemento (etiqueta-emisor ?etiqueta-izquierda)
                          (etiqueta-receptor ?etiqueta-derecha)
                          (elemento-enviado $?elemento1-izquierda)
                          (numero-copias 1)))

  (if (neq (length $?elemento2-izquierda) 0)
    then (assert (envia-elemento (etiqueta-emisor ?etiqueta-izquierda)
                                 (etiqueta-receptor ?etiqueta-derecha)
                                 (elemento-enviado $?elemento2-izquierda)
                                 (numero-copias 1))))

  (if (neq (length $?elemento1-derecha) 0)
    then (if (eq $?elemento1-derecha $?elemento2-derecha)
           then (assert (envia-elemento (etiqueta-emisor ?etiqueta-derecha)
                                       (etiqueta-receptor ?etiqueta-izquierda)
                                       (elemento-enviado $?elemento1-derecha)
                                       (numero-copias 2)))

           else (assert (envia-elemento (etiqueta-emisor ?etiqueta-derecha)
                                        (etiqueta-receptor ?etiqueta-izquierda)
                                        (elemento-enviado $?elemento1-derecha)
                                        (numero-copias 1)))

                (if (neq (length $?elemento2-derecha) 0)
                  then (assert (envia-elemento (etiqueta-emisor ?etiqueta-derecha)
                                        (etiqueta-receptor ?etiqueta-izquierda)
                                        (elemento-enviado $?elemento2-derecha)
                                        (numero-copias 1))))))

)

(defrule realiza-envio "envia, de una membrana a otra, los elementos determinados por una regla de comunicacion concreta"
  (declare (salience 94)) ;Antes de aplicar alguna regla nueva de comunicacion o division hay que realizar los envios pendientes
                          ; de la regla de comunicacion recien disparada y que ha generado la activacion de esta regla.

  ?envio <- (envia-elemento (etiqueta-emisor ?etiqueta-emisor)
                            (etiqueta-receptor ?etiqueta-receptor)
                            (elemento-enviado $?elemento-enviado)
                            (numero-copias ?n-copias))

  ?membrana-emisora <- (membrana (etiqueta ?etiqueta-emisor)
                                (estado comunicacion)
                                (contenido $?cei , $?elemento-enviado , $?cef))

  ?membrana-receptora <- (membrana (etiqueta ?etiqueta-receptor)
                                  (estado comunicacion)
                                  (contenido $?cr))
  =>
  (retract ?envio)
  (modify ?membrana-emisora (contenido $?cei , $?cef))
  (modify ?membrana-receptora (contenido $?cr $?elemento-enviado ,))

  (if (> ?n-copias 1)
    then (assert (envia-elemento (etiqueta-emisor ?etiqueta-emisor)
                              (etiqueta-receptor ?etiqueta-receptor)
                              (elemento-enviado $?elemento-enviado)
                              (numero-copias (- ?n-copias 1)))))

)

(defrule inicia-fase-generacion "realiza los cambios pertinenetes en el sistema para que empiece la fase de generacion"

  ;Se han inicializado todos los componentes del sistema.
  ; ?constantes <- (constantes)
  ; ?vertices <- (vertices)
  ; ?aristas <- (aristas)
  ; ?reglas <- (reglas)
  ; ?contadores-a <- (contadores a)
  ?contadores-c <- (contadores c)
  ; ?contadores-d <- (contadores d)
  ; ?contadores-f <- (contadores f)

  ;Membranas que se encuentran en fase de inicializacion.
  ?entorno <- (membrana (etiqueta 0)
                        (estado inicializacion))

  ?entrada <- (membrana (etiqueta 2)
                        (estado inicializacion))

  =>
  ;(retract ?constantes ?vertices ?aristas ?reglas ?contadores-a ?contadores-c ?contadores-d ?contadores-f)
  (retract ?contadores-c)
  (modify ?entrada (estado division))
  (modify ?entorno (estado comunicacion))

)

(defrule inicia-fase-verificacion "realiza los cambios pertinenetes en el sistema para que empiece la fase de verificacion"
  ;Cuando el contador c en la membrana etiquetada por 1 llegue al paso 2n se inicia la fase de verificacion.
  ; En el paso 2n el indice del ultimo contador es 2n+1.

  ?membrana1 <- (membrana (etiqueta 1)
                          (estado comunicacion)
                          (contenido ?$ci1 , c =(+ (* 2 ?*n-vertices*) 1) , ?$cf2))

  ?membrana2 <- (membrana (etiqueta 2)
                          (estado division))

  =>
  (modify ?membrana2 (estado comunicacion))

)

;EJEMPLOS DE INSTANCIAS DEL PROBLEMA 3-COL

(deffacts ejemplo1-instancia-3-col "datos de ejemplo de un problema 3-COL" ;Existe solucion 3-COL.
  (instancia-3col (n-vertices 3) (vertices , A 1 , A 2 , A 3 ,)
                  (m-aristas 3) (aristas , A 1 2 , A 1 3 , A 2 3 ,))

)

; (deffacts ejemplo2-instancia-3-col "datos de ejemplo de un problema 3-COL" ;No existe solucion 3-COL.
;   (instancia-3col (n-vertices 4) (vertices , A 1 , A 2 , A 3 , A 4 ,)
;                   (m-aristas 4) (aristas , A 1 2 , A 1 3 , A 1 4 , A 2 3 , A 2 4 , A 3 4 ,))
; )

; (deffacts ejemplo3-instancia-3-col "datos de ejemplo de un problema 3-COL" ;Existe solucion 2-COL
;   (instancia-3col (n-vertices 4) (vertices , A 1 , A 2 , A 3 , A 4 ,)
;                   (m-aristas 4) (aristas , A 1 2 , A 1 3 , A 1 4 ,))
; )
