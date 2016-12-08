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

  ;El campo estado tiene como objetivo modelar el comportamiento respecto al proceso de division celular
  ; de los sistemas p basado en tejidos. De manera que, una membrana que va a dividirse no puede ser objeto
  ; de ninguna comunicacion con otras membranas. Ademas se usara para determinar la fase de inicializacion
  ; en la que se introduciran los elementos especificos de la instancia del problema 3-COL a resolver.

  (slot etiqueta
    (type INTEGER))
  (slot identificador
    (type INTEGER))
  (slot estado
    (allowed-values inicializacion division comunicacion))
  (slot configuracion
    (allowed-values actual siguiente))
  (multislot contenido)

)

(deftemplate regla-division "datos que definen una regla de division para el sistema p"

  ;[elemento-izquierda](etiqueta) -> [elemento1-derecha](etiqueta)[elemento2-derecha](etiqueta)

  (slot etiqueta
    (type INTEGER))
  (multislot elemento-izquierda)
  (multislot elemento1-derecha)
  (multislot elemento2-derecha)

)

(deftemplate regla-comunicacion "datos que definen una regla de comunicacion para el sistema p"

  ;(etiqueta-izquierda, elemento1-izquierda elemento2-izquierda/elemento1-derecha elemento2-derecha, etiqueta-derecha)

  ;Una regla de comunicacion tiene como maximo 4 elementos, 2 maximo por parte de la membrana con etiqueta-izquierda
  ; y otros 2 maximo por parte de la membrana con etiqueta-derecha. Los elementos especificados de cada membrana seran
  ; los intercambiados entre las mismas.

  (slot etiqueta-izquierda
    (type INTEGER))
  (multislot elemento1-izquierda)
  (multislot elemento2-izquierda)
  (slot etiqueta-derecha
    (type INTEGER))
  (multislot elemento1-derecha)
  (multislot elemento2-derecha)

)

(deftemplate envia-elemento "modela el envio de un elemento desde una membrana a otra"
  (slot etiqueta-emisor
    (type INTEGER))
  (slot etiqueta-receptor
    (type INTEGER))
  (multislot elemento-enviado)
  (slot numero-copias)

)

(deftemplate instancia-3col "define una instancia del problema 3-COL a partir del grafo que la codifica"
  (slot n-vertices
    (type INTEGER))
  (multislot vertices) ;(vertices , A 1 , A 2 , ... , An ,)
  (slot m-aristas
    (type INTEGER))
  (multislot aristas)  ;(aristas , A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

)

;FUNCIONES AUXILIARES
(deffunction techo (?valor) "calcula la funcion matematica techo del valor pasado como parametro"
  (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))

)

;VARIABLES GLOBALES
(defglobal ?*n-vertices* = 0   ;Numero de vertices que codifican las distintas regiones del mapa.
           ?*m-aristas* = 0    ;Numero de aristas que codifican las fronteras entre regiones del mapa.
           ?*techo-log2-m* = 0 ;Valor necesario para la generacion de ciertos elementos en funcion de la instancia del problema.
           ?*id* = 2)          ;Valor de referencia para identificar nuevas membranas producto de la mitosis de otra.

;REGLAS (INICIALIZACION, DIVISION y COMUNICACION)
;TODO Incluir mensajes descriptivos del proceso para determinar cuando empieza el proceso real.
;TODO Implementar regla para mostrar el resultado final a partir de la entrada dada.
;TODO Implementar regla para lanzar interfaz de usuario e introducir instancias del problema manualmente o elegir de entre los 2 ejemplos propuestos.

;INICIALIZACION
(defrule lee-instancia-3-col "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  ;ESTRUCTURA DE MEMBRANAS
  (assert
          ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con los elementos que codifican una instancia
          ; del problema 3-COL. Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
          ;Se supone que el entorno contiene el numero suficiente de copias de cada elemento.
          (membrana (etiqueta 0)
                    (identificador 0)
                    (estado inicializacion)
                    (contenido , b , D , E , e , T , S , N , z ,)) ;Constantes presentes para cualquier instancia del problema.

          (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
                    (identificador 1)
                    (estado comunicacion)
                    (contenido , a 1 , b , c 1 , yes , no ,))

          ;La membrana 2 contiene, entre otros, los elementos de entrada que codifican una instancia del problema 3-COL.
          ; Por tanto tambien requiere ser inicializada con dichos elementos.
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
  (assert (inicializa-vertices ?n-vertices $?vertices) ;(, A 1 , A 2 , ... , A n ,)
          (inicializa-aristas ?m-aristas $?aristas))   ;(, A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

  ;CONTADORES
  ;Hechos para la inicializacion de los distintos tipos de contadores del sistema.
  (assert (inicializa-contadores a)
          (inicializa-contadores c)
          (inicializa-contadores d)
          (inicializa-contadores f))

)

(defrule inicializacion-vertices "introduce en el sistema los elementos referentes a los vertices"
  (declare (salience 99)) ;Se inicializan en primer lugar.

  ?iv <- (inicializa-vertices ?pendientes $?vi , A ?i , $?vf)

  ?entorno <- (membrana (etiqueta 0)
                        (estado inicializacion)
                        (contenido $?c0))

  ?entrada <- (membrana (etiqueta 2)
                        (estado inicializacion)
                        (contenido $?c2))

  =>
  (retract ?iv)
  (modify ?entorno (contenido $?c0 A ?i , R ?i , T ?i , B ?i , G ?i , RC ?i , BC ?i , GC ?i ,))
  (modify ?entrada (contenido $?c2 A ?i ,))

  ;Reglas asociadas a los vertices.
  (assert ;REGLAS DE DIVISION
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
                              (elemento1-derecha z)))

  ;Comprueba si existen vertices que no han sido procesados.
  (if (neq ?pendientes 1)
    then (assert (inicializa-vertices (- ?pendientes 1) $?vi , $?vf))

    else (assert (vertices))) ;Se han incluido todos los elementos de los vertices en las membranas correspondientes.

)

(defrule inicializacion-aristas "introduce en el sistema los elementos referentes a las aristas"
    (declare (salience 97)) ;Se inicializan en ultimo lugar.

    ?ia <- (inicializa-aristas ?pendientes $?ai , A ?i ?j , $?af)

    ?entorno <- (membrana (etiqueta 0) ;Entorno
                            (estado inicializacion)
                            (contenido $?c0))

    ?entrada <- (membrana (etiqueta 2) ;Entrada
                            (estado inicializacion)
                            (contenido $?c2))

  =>
  (retract ?ia)
  (modify ?entorno (contenido $?c0 P ?i ?j , PC ?i ?j , R ?i ?j , B ?i ?j , G ?i ?j ,))
  (modify ?entrada (contenido $?c2 A ?i ?j ,))

  ;Reglas asociadas a las aristas.
  ;REGLAS DE COMUNICACION (2 <-> 0)
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
  (declare (salience 98)) ;Se inicializan en segundo lugar.

  ?ic <- (inicializa-contadores ?tipo)

  ?entorno <- (membrana (etiqueta 0)
                        (estado inicializacion)
                        (contenido $?c0))

  =>
  (retract ?ic)

  (switch ?tipo
      (case a ;1 ... 2n + [log2(m)] + 12
        then (bind ?indice-a 1)
             (bind ?contadores (create$ ?tipo ?indice-a ,))
             (bind ?limite-a (+ (*  2 ?*n-vertices*) ?*techo-log2-m* 12))

             ;Genera la lista de elementos referentes al contador correspondiente.
             (while (< ?indice-a ?limite-a)

                ;Regla asociada al contador a con indice i
                ;REGLA DE COMUNICACION (1 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 1) ;r3i
                                            (elemento1-izquierda a ?indice-a)
                                            (etiqueta-derecha 0)
                                            (elemento1-derecha a (+ ?indice-a 1))))

                (bind ?indice-a (+ ?indice-a 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-a ,))))

      (case c ;1 ... 2n + 1
        then (bind ?indice-c 1)
             (bind ?contadores (create$ ?tipo ?indice-c ,))
             (bind ?limite-c (+ (* 2 ?*n-vertices*) 1))
             (while (< ?indice-c ?limite-c)

                ;Regla asociada al contador c con indice i
                ;REGLA DE COMUNICACION (1 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 1) ;r4i
                                            (elemento1-izquierda c ?indice-c)
                                            (etiqueta-derecha 0)
                                            (elemento1-derecha c (+ ?indice-c 1))
                                            (elemento2-derecha c (+ ?indice-c 1))))

                (bind ?indice-c (+ ?indice-c 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-c ,))))

      (case d ;1 ... [log2(m)] + 1
        then (bind ?indice-d 1)
             (bind ?contadores (create$ ?tipo ?indice-d ,))
             (bind ?limite-d (+ ?*techo-log2-m* 1))
             (while (< ?indice-d ?limite-d)

                ;Regla asociada al contador d con indice i
                ;REGLA DE COMUNICACION (2 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 2) ;r7i
                                            (elemento1-izquierda d ?indice-d)
                                            (etiqueta-derecha 0)
                                            (elemento1-derecha d (+ ?indice-d 1))
                                            (elemento2-derecha d (+ ?indice-d 1))))

                (bind ?indice-d (+ ?indice-d 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-d ,))))

      (case f ;2 ... [log2(m)] + 7
        then (bind ?indice-f 2)
             (bind ?contadores (create$ ?tipo ?indice-f ,))
             (bind ?limite-f (+ ?*techo-log2-m* 7))
             (while (< ?indice-f ?limite-f)

                ;Regla asociada al contador f con indice i
                ;REGLA DE COMUNICACION (2 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 2) ;r9i
                                           (elemento1-izquierda f ?indice-f)
                                           (etiqueta-derecha 0)
                                           (elemento1-derecha f (+ ?indice-f 1))))

                (bind ?indice-f (+ ?indice-f 1))
                (bind ?contadores (insert$ ?contadores 1 ?tipo ?indice-f ,)))))

  (modify ?entorno (contenido $?c0 ?contadores))
  (assert (contadores ?tipo)) ;Se han incluido todos los contadores del tipo indicado.

)

;DIVISION
(defrule division "crea dos nuevas membranas en sustitucion de una existente y a partir de una regla de division concreta"

  ;Selecciona los elementos que definen la regla de division
  (regla-division (etiqueta ?etiqueta)
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
                      (elemento1-derecha $?elemento1-derecha)     ;Puede ser vacio, si este elemtno es vacio el segundo tambien lo es.
                      (elemento2-derecha $?elemento2-derecha))    ;Puede ser vacio

  ;A continuacion se recoge toda la casuistica para toda posible comunicacion en la familia p que resuelve el problema 3-COL.
  (or   ;La membrana especificada en la parte izquierda de la regla envia 2 elementos. (Antiport)
        (and (membrana (etiqueta ?etiqueta-izquierda)
                       (identificador ?idi)
                       (estado comunicacion)
                       (contenido $? , $?elemento1-izquierda , $?))

             (membrana (etiqueta ?etiqueta-izquierda)
                       (identificador ?idi)
                       (estado comunicacion)
                       (contenido $? , $?elemento2-izquierda , $?)))

        ;La membrana especificada en la parte izquierda de la regla envia 1 elemento. (Antiport)
        (and (membrana (etiqueta ?etiqueta-izquierda)
                   (estado comunicacion)
                   (contenido $?, $?elemento1-izquierda , $?))

             (test (= (length $?elemento2-izquierda) 0))))

  (or
        ;La membrana especificada en la parte derecha de la regla envia 2 elementos diferentes. (Antiport)
        (and (membrana (etiqueta ?etiqueta-derecha)
                       (identificador ?idd)
                       (estado comunicacion)
                       (contenido $? , $?elemento1-derecha , $?))

             (membrana (etiqueta ?etiqueta-derecha)
                       (identificador ?idd)
                       (estado comunicacion)
                       (contenido $? , $?elemento2-derecha , $?))

             (test (neq $?elemento1-derecha $?elemento2-derecha)))


        ;La membrana especificada en la parte derecha de la regla envia 2 elementos iguales. (Antiport)
        (and  (membrana (etiqueta ?etiqueta-derecha)
                        (estado comunicacion)
                        (contenido $? , $?elemento1-derecha , $?))

              (test (eq $?elemento1-derecha $?elemento2-derecha)))

        ;La membrana especificada en la parte derecha de la regla envia 1 elemento. (Antiport)
        (and (membrana (etiqueta ?etiqueta-derecha)
                       (estado comunicacion)
                       (contenido $? , $?elemento1-derecha , $?))

             (test (= (length $?elemento2-derecha) 0)))

        ;La membrana especificada en la parte derecha de la regla no envia ningun elemento. (Symport)
        (and (test (= (length $?elemento1-derecha) 0))
             (test (= (length $?elemento2-derecha) 0))))

  =>
  (assert (envia-elemento (etiqueta-emisor ?etiqueta-izquierda)
                          (etiqueta-receptor ?etiqueta-derecha)
                          (elemento-enviado $?elemento1-izquierda)
                          (numero-copias 1)))

  (if (neq (length $?elemento2-izquierda) 0) ;Existe un segundo elemento que enviar por parte de la membrana con ?etiqueta-izquierda.
    then (assert (envia-elemento (etiqueta-emisor ?etiqueta-izquierda)
                                 (etiqueta-receptor ?etiqueta-derecha)
                                 (elemento-enviado $?elemento2-izquierda)
                                 (numero-copias 1))))

  (if (neq (length $?elemento1-derecha) 0) ;Existen elementos a enviar por parte de la membrana con ?etiqueta-derecha.
    then (if (eq $?elemento1-derecha $?elemento2-derecha) ;Envia dos elementos iguales.
           then (assert (envia-elemento (etiqueta-emisor ?etiqueta-derecha)
                                       (etiqueta-receptor ?etiqueta-izquierda)
                                       (elemento-enviado $?elemento1-derecha)
                                       (numero-copias 2)))

           else (assert (envia-elemento (etiqueta-emisor ?etiqueta-derecha)
                                        (etiqueta-receptor ?etiqueta-izquierda)
                                        (elemento-enviado $?elemento1-derecha)
                                        (numero-copias 1)))

                (if (neq (length $?elemento2-derecha) 0) ;Envia dos elementos diferentes.
                  then (assert (envia-elemento (etiqueta-emisor ?etiqueta-derecha)
                                        (etiqueta-receptor ?etiqueta-izquierda)
                                        (elemento-enviado $?elemento2-derecha)
                                        (numero-copias 1))))))

)

(defrule realiza-envio "envia, de una membrana a otra, los elementos determinados por una regla de comunicacion concreta"
  (declare (salience 96)) ;Antes de aplicar alguna regla nueva de comunicacion o division hay que realizar los envios pendientes
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

  ;Genera las copias necesarias si ha enviado mas de un elemento identico.
  (bind ?elementos (create$ $?elemento-enviado ,))
  (while (> ?n-copias 1)
    (bind ?elementos (insert$ ?elementos 1 $?elemento-enviado ,)) ;TODO aqui mete un FALSE por que sí loco
    (bind ?n-copias (- ?n-copias 1)))

  (modify ?membrana-receptora (contenido $?cr ?elementos))

  (if (neq ?etiqueta-emisor 0) ;Si la emisora no es el entorno hay que eliminar el elemento de su region.
    then   (modify ?membrana-emisora (contenido $?cei , $?cef)))

  ;En el caso del entorno, se supone que contiene los elementos necesarios en un numero suficiente de copias,
  ; consideramos que siempre habra de los elementos requeridos por lo que para que el sistema funcione de manera mas
  ; eficiente con respecto a la equiparacion de patrones de CLIPS se ha optado por no elimnar los objetos del mismo.

)

(defrule inicia-fase-generacion "realiza los cambios pertinenetes en el sistema para que empiece la fase de generacion"

  ;Se han inicializado todos los componentes del sistema.
  ?vertices <- (vertices)
  ?contadores-a <- (contadores a)
  ?contadores-c <- (contadores c)
  ?contadores-d <- (contadores d)
  ?contadores-f <- (contadores f)
  ?aristas <- (aristas)

  ;Membranas que se encuentran en fase de inicializacion.
  ?entorno <- (membrana (etiqueta 0)
                        (estado inicializacion))

  ?entrada <- (membrana (etiqueta 2)
                        (estado inicializacion))

  =>
  (retract ?vertices ?contadores-a ?contadores-c ?contadores-d ?contadores-f ?aristas)
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
