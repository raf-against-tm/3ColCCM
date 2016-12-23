;SOLUCION PARA EL PROBLEMA 3-COL MEDIANTE COMPUTACION CELULAR CON MEMBRANAS.

;RAFAEL VALLE MORALES. INGENIERIA INFORMATICA (PLAN 97)

;[ARCHIVO SIN TILDES]

;El problema 3-COL consiste en determinar si un mapa puede ser coloreado unicamente con 3 colores, teniendo
; en cuenta que las regiones contiguas deben tener colores distintos. Toda instancia del problema es codificada
; por un grafo cuyos vertices determinan las distintas regiones del mapa, y cuyas aristas definen las fronteras entre
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

  (slot etiqueta
    (type INTEGER))
  (slot identificador
    (type INTEGER))
  (slot configuracion
    (type INTEGER)
    (default 0))
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

  (slot identificador-emisor
    (type INTEGER))
  (slot identificador-receptor
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

;HECHOS INICIALES
(deffacts datos-computacion "conjunto de hechos necesarios para controlar los pasos de la computacion"
  (paso-actual 0)
  (paso-siguiente 1)

  ;Hecho que define el estado actual del sistema. Se usa para llevar a cabo la inicializacion del sistema,
  ; la aplicacion de reglas en una transicion y la actualizacion de las estrucutras de datos para pasar
  ; de una configuracion a otra. Toma los valores 'inicializacion', 'transicion' y 'actualizacion'.
  (estado inicializacion)

)

;INSTANCIAS DEL PROBLEMA 3-COL DE EJEMPLO
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

;VARIABLES GLOBALES
(defglobal ?*n-vertices*   = 0  ;Numero de vertices que codifican las distintas regiones del mapa.
           ?*m-aristas*    = 0  ;Numero de aristas que codifican las fronteras entre regiones del mapa.
           ?*techo-log2-m* = 0  ;Valor necesario para la generacion de ciertos elementos en funcion de la instancia del problema.
           ?*id*           = 2) ;Valor de referencia para identificar nuevas membranas producto de la division celular.

;FUNCIONES AUXILIARES
(deffunction techo (?valor) "calcula la funcion matematica techo del valor pasado como parametro"
 (if (> ?valor (integer ?valor)) then (+ (integer ?valor) 1) else (integer ?valor))

)

;REGLAS (INICIALIZACION, CONTROL DE LA COMPUTACION, DIVISION y COMUNICACION)
;INICIALIZACION
(defrule lee-instancia-3-col "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  (assert ;ESTRUCTURA DE MEMBRANAS

    ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con los elementos que codifican una instancia
    ; del problema 3-COL. Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
    (membrana (etiqueta 0)
              (identificador 0)
              (contenido , b , D , E , e , T , S , N , z ,)) ;Constantes presentes para cualquier instancia del problema.

    (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
              (identificador 1)
              (contenido , a 1 , b , c 1 , yes , no ,))

    ;La membrana 2 contiene, entre otros, los elementos de entrada que codifican una instancia del problema 3-COL. Por tanto
    ; tambien requiere ser inicializada con dichos elementos.
    (membrana (etiqueta 2)
              (identificador 2)
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

  (estado inicializacion)

  ?iv <- (inicializa-vertices ?pendientes $?vi , A ?i , $?vf)

  ?entorno <- (membrana (etiqueta 0)
                        (contenido $?c0))

  ?entrada <- (membrana (etiqueta 2)
                        (contenido $?c2))

  =>
  (retract ?iv)
  (modify ?entorno (contenido $?c0 A ?i , R ?i , T ?i , B ?i , G ?i , RC ?i , BC ?i , GC ?i ,))
  (modify ?entrada (contenido $?c2 A ?i ,))

  ;Reglas asociadas a los vertices.
  ;REGLAS DE DIVISION
  (assert (regla-division (etiqueta 2) ;r1i
                           (elemento-izquierda A ?i)
                           (elemento1-derecha R ?i)
                           (elemento2-derecha T ?i))

          (regla-division (etiqueta 2) ;r2i
                           (elemento-izquierda T ?i)
                           (elemento1-derecha B ?i)
                           (elemento2-derecha G ?i)))

   ;REGLAS DE COMUNICACION (2 <-> 0)
   (assert (regla-comunicacion (etiqueta-izquierda 2) ;r16i
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
  (if (<> ?pendientes 1)
    then (assert (inicializa-vertices (- ?pendientes 1) $?vi , $?vf))

    else (assert (vertices))) ;Se han incluido todos los elementos de los vertices en las membranas correspondientes.

)

(defrule inicializacion-aristas "introduce en el sistema los elementos referentes a las aristas"
    (declare (salience 97)) ;Se inicializan en ultimo lugar.

    (estado inicializacion)

    ?ia <- (inicializa-aristas ?pendientes $?ai , A ?i ?j , $?af)

    ?entorno <- (membrana (etiqueta 0)
                          (contenido $?c0))

    ?entrada <- (membrana (etiqueta 2)
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
  (if (<> ?pendientes 1)
    then (assert (inicializa-aristas (- ?pendientes 1) $?ai , $?af))

    else (assert (aristas))) ;Se han incluido todos los elementos de las aristas en las membranas correspondientes.

)

(defrule inicializacion-contadores "genera los contadores necesarios en el entorno"
  (declare (salience 98)) ;Se inicializan en segundo lugar.

  (estado inicializacion)

  ?ic <- (inicializa-contadores ?tipo)

  ?entorno <- (membrana (etiqueta 0)
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

(defrule inicia-computacion "realiza los cambios pertinenetes en el sistema para que empiece la computacion"

  ?estado <- (estado inicializacion)

  ;Se han inicializado todos los componentes del sistema.
  ?vertices <- (vertices)
  ?contadores-a <- (contadores a)
  ?contadores-c <- (contadores c)
  ?contadores-d <- (contadores d)
  ?contadores-f <- (contadores f)
  ?aristas <- (aristas)

  ;Membranas en fase de inicializacion.
  (membrana (etiqueta 0) ;Entorno
            (contenido $?c0))

  (membrana (etiqueta 1)
            (contenido $?c1))

  (membrana (etiqueta 2) ;Entrada
            (contenido $?c2))

  =>
  (retract ?estado ?vertices ?contadores-a ?contadores-c ?contadores-d ?contadores-f ?aristas)
  (assert (estado transicion))

  ;Incluye copias de las membranas 0, 1 y 2 con el indice de la configuracion siguiente.
  (assert (membrana (etiqueta 0)
                    (identificador 0)
                    (configuracion 1)
                    (contenido $?c0))

          (membrana (etiqueta 1)
                    (identificador 1)
                    (configuracion 1)
                    (contenido $?c1))

          (membrana (etiqueta 2)
                    (identificador 2)
                    (configuracion 1)
                    (contenido $?c2)))

)

;DIVISION
(defrule division "crea dos nuevas membranas en sustitucion de una existente y a partir de una regla de division concreta"
  ;Si se aplica una regla de division, en el mismo paso de la transicion no podra aplicarse ninguna otra regla ya sea
  ; de division o de comunicacion. Este hecho se controla con el campo evolucion pues tiene que ser obligatoriamente 0, lo que
  ; indica que a dicha membrana no se le ha aplicado niguna otra regla. Por otra parte, al aplicarla se eliminan las membranas
  ; con configuracion actual por lo que no podra volverse a interactuar con ella hasta el siguiente paso de la transicion.

  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ;Selecciona los elementos que definen la regla de division
  (regla-division (etiqueta ?etiqueta)
                  (elemento-izquierda $?elemento-izquierda)
                  (elemento1-derecha $?elemento1-derecha)
                  (elemento2-derecha $?elemento2-derecha))

  ?membrana1 <- (membrana (etiqueta ?etiqueta)
                          (identificador ?id)
                          (configuracion ?pactual)
                          (contenido $?ci , $?elemento-izquierda , $?cf))

  ?membrana2 <- (membrana (identificador ?id)
                          (configuracion ?psiguiente))

  =>
  (retract ?membrana1 ?membrana2)

  (assert (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 1))
                    (configuracion ?psiguiente)
                    (contenido $?ci , $?elemento1-derecha , $?cf))

          (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 2))
                    (configuracion ?psiguiente)
                    (contenido $?ci , $?elemento2-derecha , $?cf)))

  (bind ?*id* (+ ?*id* 2)) ;Incrementa el valor referencia del identificador de membranas.

)

;COMUNICACION
(defrule comunicacion "construye los hechos que modelan la comunicacion entre dos membranas a partir una regla de comunicacion concreta"
  ;En un paso de la transicion pueden aplicarse varias reglas de comunicacion en caso de que en la membrana existan elementos que activen
  ; dichas reglas. Los elementos obtenidos de la aplicacion de una regla no se tienen en cuenta para la activacion de reglas hasta el
  ; siguiente paso.

  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
                      (elemento1-izquierda $?elemento1-izquierda) ;Siempre hay un valor
                      (elemento2-izquierda $?elemento2-izquierda) ;Puede ser vacio
                      (etiqueta-derecha ?etiqueta-derecha)
                      (elemento1-derecha $?elemento1-derecha)     ;Puede ser vacio
                      (elemento2-derecha $?elemento2-derecha))    ;Puede ser vacio

  (or ;PARTE IZQUIERDA DE LA REGLA.
      ;La membrana especificada en la parte izquierda de la regla envia 1 elemento. (Antiport)
      (and (test (= (length $?elemento2-izquierda) 0))

           (membrana (etiqueta ?etiqueta-izquierda)
                     (identificador ?id-izquierda)
                     (configuracion ?pactual)
                     (contenido $?, $?elemento1-izquierda , $?)))

      ;La membrana especificada en la parte izquierda de la regla envia 2 elementos. (Antiport)
      (and (membrana (etiqueta ?etiqueta-izquierda)
                     (identificador ?id-izquierda)
                     (configuracion ?pactual)
                     (contenido $? , $?elemento1-izquierda , $?))

           (membrana (etiqueta ?etiqueta-izquierda)
                     (identificador ?id-izquierda)
                     (configuracion ?pactual)
                     (contenido $? , $?elemento2-izquierda , $?))))

  (or ;PARTE DERECHA DE LA REGLA.
      ;Se trata de una comunicacion con el entorno.
      (and
        (test (= ?etiqueta-derecha 0))

        (membrana (etiqueta 0)
                  (identificador ?id-derecha)
                  (configuracion ?pactual)))

      ;La membrana especificada en la parte derecha de la regla no envia ningun elemento. (Symport)
      (and
        (test (= (length $?elemento1-derecha) 0)) ; Si el elemento 1 es vacio el segundo tambien lo es.

        (membrana (etiqueta ?etiqueta-derecha)
                  (identificador ?id-derecha)
                  (configuracion ?pactual)))

      (and ;La membrana especificada en la parte derecha de la regla envia 1 elemento. (Antiport)
        (test (<> ?etiqueta-derecha 0))
        (test (<> (length $?elemento1-derecha) 0))
        (test (= (length $?elemento2-derecha) 0))

        (membrana (etiqueta ?etiqueta-derecha)
                  (identificador ?id-derecha)
                  (configuracion ?pactual)
                  (contenido $? , $?elemento1-derecha , $?)))

      (and ;La membrana especificada en la parte derecha de la regla envia 2 elementos. (Antiport)
        (test (<> ?etiqueta-derecha 0))
        (test (<> (length $?elemento1-derecha) 0))
        (test (<> (length $?elemento2-derecha) 0))

        (membrana (etiqueta ?etiqueta-derecha)
                  (identificador ?id-derecha)
                  (configuracion ?pactual)
                  (contenido $?cdi1 , $?elemento1-derecha , $?cdf1))

        (membrana (etiqueta ?etiqueta-derecha)
                  (identificador ?id-derecha)
                  (configuracion ?pactual)
                  (contenido $?cdi2 , $?elemento2-derecha , $?cdf2))

        ;Comprueba que no selecciona el mismo elemento 2 veces en caso de que sean iguales.
        (test (neq $?cdi1 $?cdi2))
        (test (neq $?cdf1 $?cdf2)))

    )

  =>
  (assert (envia-elemento (identificador-emisor ?id-izquierda) ;En toda comunicacion hay al menos un elemento que es enviado.
                          (identificador-receptor ?id-derecha)
                          (elemento-enviado $?elemento1-izquierda)
                          (numero-copias 1)))

  (if (<> (length $?elemento2-izquierda) 0) ;Existe un segundo elemento que enviar por parte de la membrana con id ?id-izquierda
    then (assert (envia-elemento (identificador-emisor ?id-izquierda)
                                 (identificador-receptor ?id-derecha)
                                 (elemento-enviado $?elemento2-izquierda)
                                 (numero-copias 1))))

  (if (<> (length $?elemento1-derecha) 0) ;Existen elementos a enviar por parte de la membrana con con id ?id-derecha
    then (if (eq $?elemento1-derecha $?elemento2-derecha) ;Envia dos elementos iguales.
           then (assert (envia-elemento (identificador-emisor ?id-derecha)
                                        (identificador-receptor ?id-izquierda)
                                        (elemento-enviado $?elemento1-derecha)
                                        (numero-copias 2)))

           else (assert (envia-elemento (identificador-emisor ?id-derecha)
                                        (identificador-receptor ?id-izquierda)
                                        (elemento-enviado $?elemento1-derecha)
                                        (numero-copias 1)))

                (if (<> (length $?elemento2-derecha) 0) ;Envia dos elementos diferentes.
                  then (assert (envia-elemento (identificador-emisor ?id-derecha)
                                               (identificador-receptor ?id-izquierda)
                                               (elemento-enviado $?elemento2-derecha)
                                               (numero-copias 1))))))

)

(defrule realiza-envio "envia, de una membrana a otra, los elementos determinados por una regla de comunicacion concreta"
  (declare (salience 96)) ;Antes de aplicar alguna regla nueva de comunicacion o division hay que realizar los envios pendientes
                          ; de la regla de comunicacion recien disparada y que ha generado la activacion de esta regla.

  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ?envio <- (envia-elemento (identificador-emisor ?id-emisor)
                            (identificador-receptor ?id-receptor)
                            (elemento-enviado $?elemento-enviado)
                            (numero-copias ?n-copias))

  ?membrana-emisora1  <- (membrana (identificador ?id-emisor)
                                   (configuracion ?pactual)
                                   (contenido $?cei1 , $?elemento-enviado , $?cef1))

  ?membrana-emisora2  <- (membrana (identificador ?id-emisor)
                                   (configuracion ?psiguiente)
                                   (contenido $?cei2 , $?elemento-enviado , $?cef2))

  ?membrana-receptora <- (membrana (identificador ?id-receptor)
                                   (configuracion ?psiguiente)
                                   (contenido $?cr))

  =>
  (retract ?envio)

  ;El entorno contiene un numero suficiente de copias para todo elemento necesario en el proceso, por ello
  ; consideramos que dichos elementos del entorno no son alterados por la aplicacion de reglas.

  (if (<> ?id-emisor 0) ;Si el emisor no es el entorno, hay que eliminar el elemento de su contenido.
    then (modify ?membrana-emisora1 (contenido $?cei1 , $?cef1))
         (modify ?membrana-emisora2 (contenido $?cei2 , $?cef2)))

  ;Genera las copias necesarias si ha enviado mas de un elemento identico.
  (bind ?elementos (create$ $?elemento-enviado ,))
  (while (> ?n-copias 1)
    (bind ?elementos (insert$ ?elementos 1 $?elemento-enviado ,))
    (bind ?n-copias (- ?n-copias 1)))

  ;Para que el proceso no se vea afectado en exceso por la equiparacion de patrones con los elementos
  ; del entorno, solo se enviaran los elementos al mismo cuando se trate de aquellos que definen la solucion del problema.
  (if (or (<> ?id-receptor 0) (eq $?elemento-enviado yes) (eq $?elemento-enviado no))
    then (modify ?membrana-receptora (contenido $?cr ?elementos)))

)

(defrule finaliza-transicion "comprueba si queda alguna regla de comunicacion por aplicar en la configuracion actual"

  ?estado <- (estado transicion)

  (paso-actual ?pactual)

  ;Comprueba que no queda ninguna regla de comunicacion que se pueda aplicar.
  (not
    (and
      (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
                          (elemento1-izquierda $?elemento1-izquierda) ;Siempre hay un valor
                          (elemento2-izquierda $?elemento2-izquierda) ;Puede ser vacio
                          (etiqueta-derecha ?etiqueta-derecha)
                          (elemento1-derecha $?elemento1-derecha)     ;Puede ser vacio
                          (elemento2-derecha $?elemento2-derecha))    ;Puede ser vacio

      (or ;PARTE IZQUIERDA DE LA REGLA.
          ;La membrana especificada en la parte izquierda de la regla envia 1 elemento. (Antiport)
          (and (test (= (length $?elemento2-izquierda) 0))

               (membrana (etiqueta ?etiqueta-izquierda)
                         (identificador ?id-izquierda)
                         (configuracion ?pactual)
                         (contenido $?, $?elemento1-izquierda , $?)))

          ;La membrana especificada en la parte izquierda de la regla envia 2 elementos. (Antiport)
          (and (membrana (etiqueta ?etiqueta-izquierda)
                         (identificador ?id-izquierda)
                         (configuracion ?pactual)
                         (contenido $? , $?elemento1-izquierda , $?))

               (membrana (etiqueta ?etiqueta-izquierda)
                         (identificador ?id-izquierda)
                         (configuracion ?pactual)
                         (contenido $? , $?elemento2-izquierda , $?))))

      (or ;PARTE DERECHA DE LA REGLA.
          ;Se trata de una comunicacion con el entorno.
          (and
            (test (= ?etiqueta-derecha 0))

            (membrana (etiqueta 0)
                      (identificador ?id-derecha)
                      (configuracion ?pactual)))

          ;La membrana especificada en la parte derecha de la regla no envia ningun elemento. (Symport)
          (and
            (test (= (length $?elemento1-derecha) 0)) ; Si el elemento 1 es vacio el segundo tambien lo es.

            (membrana (etiqueta ?etiqueta-derecha)
                      (identificador ?id-derecha)
                      (configuracion ?pactual)))

          (and ;La membrana especificada en la parte derecha de la regla envia 1 elemento. (Antiport)
            (test (<> ?etiqueta-derecha 0))
            (test (<> (length $?elemento1-derecha) 0))
            (test (= (length $?elemento2-derecha) 0))

            (membrana (etiqueta ?etiqueta-derecha)
                      (identificador ?id-derecha)
                      (configuracion ?pactual)
                      (contenido $? , $?elemento1-derecha , $?)))

          (and ;La membrana especificada en la parte derecha de la regla envia 2 elementos. (Antiport)
            (test (<> ?etiqueta-derecha 0))
            (test (<> (length $?elemento1-derecha) 0))
            (test (<> (length $?elemento2-derecha) 0))

            (membrana (etiqueta ?etiqueta-derecha)
                      (identificador ?id-derecha)
                      (configuracion ?pactual)
                      (contenido $?cdi1 , $?elemento1-derecha , $?cdf1))

            (membrana (etiqueta ?etiqueta-derecha)
                      (identificador ?id-derecha)
                      (configuracion ?pactual)
                      (contenido $?cdi2 , $?elemento2-derecha , $?cdf2))

            ;Comprueba que no selecciona el mismo elemento 2 veces en caso de que sean iguales.
            (test (neq $?cdi1 $?cdi2))
            (test (neq $?cdf1 $?cdf2))))))

    =>
    (retract ?estado)
    (assert (estado actualizacion))

)


(defrule sincronizacion-actualizacion-1 "elimina las membranas con el indice de la configuracion actual"
  (estado actualizacion)
  (paso-actual ?pactual)

  ?actual <- (membrana  (etiqueta ?etiqueta)
                        (identificador ?id)
                        (configuracion ?pactual))

  =>
  (retract ?actual)

)

(defrule sincronizacion-actualizacion-2 "inserta las copias necesarias para la proxima configuracion"
  (estado actualizacion)
  (paso-siguiente ?psiguiente)

  ?siguiente <- (membrana (etiqueta ?etiqueta)
                          (identificador ?id)
                          (configuracion ?psiguiente)
                          (contenido $?c))

  =>
  ;Introduce copia con el indice de la siguiente configuracion.
  (assert (membrana (etiqueta ?etiqueta)
                    (identificador ?id)
                    (configuracion (+ ?psiguiente 1))
                    (contenido $?c)))

)

(defrule siguiente-configuracion "pasa el sistema a la siguiente configuracion"
  ?pa <- (paso-actual ?pactual)
  ?ps <- (paso-siguiente ?psiguiente)

  ?estado <- (estado actualizacion)

  ;Verifica que toda membrana tiene su copia con el indice de la configuracion siguiente a la misma.
  (forall (membrana (identificador ?id)
                    (configuracion ?psiguiente))
          (membrana (identificador ?id)
                    (configuracion ?siguiente&:(= ?siguiente (+ ?psiguiente 1)))))

  =>
  (retract ?pa ?ps ?estado)
  (assert (estado transicion))
  (assert (paso-actual ?psiguiente)
          (paso-siguiente (+ ?psiguiente 1)))

)
