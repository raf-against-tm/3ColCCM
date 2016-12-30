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
  (multislot contenido) ; , ... , copias elemento indice-1 inidice-2 ... , ... ,

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

(deftemplate envia-elemento "datos referentes al envio de un elemento desde una membrana a otra"

  (slot identificador-emisor
    (type INTEGER))
  (slot identificador-receptor
    (type INTEGER))
  (multislot elemento-enviado)

)

(deftemplate instancia-3col "datos que definen una instancia del problema 3-COL a partir del grafo que la codifica"

  (slot n-vertices
    (type INTEGER))
  (multislot vertices) ;(vertices , A 1 , A 2 , ... , An ,)
  (slot m-aristas
    (type INTEGER))
  (multislot aristas)  ;(aristas , A 1 2 , A 1 3 , ... , A i j ,) con 1 <= i < j <= n

)

;HECHOS INICIALES
(deffacts estado-inicial-computacion "conjunto de hechos necesarios para controlar los pasos de la computacion"
  (paso-actual 0)
  (paso-siguiente 1)

  ;Hecho que define el estado del sistema. Se usa para llevar a cabo la inicializacion del sistema,
  ; la aplicacion de reglas en una transicion, la actualizacion de las estrucutras de datos para pasar de una
  ; configuracion a otra y para gestionar la respuesta final de la computacion con respecto al problema inicial.
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

(deffunction agrega-elementos (?contenido ?k $?elemento) "agrega k copias del elemento dado al contenido especificado"

  ;Si hay algun elemento identico en el contenido los agrupa y si no, lo incluye en el mismo.

  (if (= (length$ $?elemento) 0) ;Se trata de un elemento vacio.
    then (return ?contenido))

  (bind ?posiciones (member$ $?elemento ?contenido))

  (if (neq ?posiciones FALSE)
    then (if (> (length$ (create$ ?posiciones)) 1)
           then (bind ?pos1    (- (nth$ 1 ?posiciones) 1))
                (bind ?pos2    (nth$ 2 ?posiciones))

           ;Cuando se trata de un elemento sin indices la variable ?posiciones es un unico valor.
           else (bind ?pos1 (- ?posiciones 1))
                (bind ?pos2 ?posiciones))


         (bind ?copias  (nth$ ?pos1 ?contenido))

         (replace$ ?contenido ?pos1 ?pos2 (create$ (+ ?k ?copias) $?elemento))

    else (insert$ ?contenido 1 , ?k $?elemento))

)

(deffunction elimina-elementos (?contenido ?k $?elemento) "elimina k copias del elemento dado en el contenido especificado"

  ;Si el elemento a eliminar no existe o no hay suficientes en el contenido devuelve FALSE

  (if (= (length$ $?elemento) 0) ;Se trata de un elemento vacio.
    then (return ?contenido))

  (bind ?posiciones (member$ $?elemento ?contenido))

  (if (neq ?posiciones FALSE)
    then (if (> (length$ (create$ ?posiciones)) 1)
           then (bind ?pos1    (- (nth$ 1 ?posiciones) 1))
                (bind ?pos2    (nth$ 2 ?posiciones))

           ;Cuando se trata de un elemento sin indices la variable ?posiciones es un unico valor.
           else (bind ?pos1 (- ?posiciones 1))
                (bind ?pos2 ?posiciones))


         (bind ?copias  (nth$ ?pos1 ?contenido))
         (bind ?restantes (- ?copias ?k))

         (if (= ?restantes 0)
           then (return (delete$ ?contenido (- ?pos1 1) ?pos2))) ;Elimina completamente el elemento.

         (if (> ?restantes 0)
           then (return (replace$ ?contenido ?pos1 ?pos1 ?restantes))))

)

(deffunction existe-elemento (?contenido ?k $?elemento) "comprueba si existen k copias del elemento dado en el contenido especificado"

  ;Si el elemento existe y hay copias suficientes devuelve TRUE.

  (if (= (length$ $?elemento) 0) ;Se trata de un elemento vacio.
    then (return TRUE))

  (bind ?posiciones (member$ $?elemento ?contenido))

  (if (neq ?posiciones FALSE)
    then (if (> (length$ (create$ ?posiciones)) 1)
           then (bind ?pos1    (- (nth$ 1 ?posiciones) 1))
                (bind ?pos2    (nth$ 2 ?posiciones))

           ;Cuando se trata de un elemento sin indices la variable ?posiciones es un unico valor.
           else (bind ?pos1 (- ?posiciones 1))
                (bind ?pos2 ?posiciones))


          (bind ?copias  (nth$ ?pos1 ?contenido))
          (bind ?restantes (- ?copias ?k))

          (return (>= ?restantes 0)))

)

;REGLAS (INICIALIZACION, CONTROL DE LA COMPUTACION, DIVISION y COMUNICACION)
;INICIALIZACION
(defrule lee-instancia-3-col "a partir de los datos de entrada genera los hechos necesarios para inicializar el sistema"

  ?entrada <- (instancia-3col (n-vertices ?n-vertices) (vertices $?vertices)
                              (m-aristas ?m-aristas) (aristas $?aristas))
  =>
  (retract ?entrada)

  ;DATOS DE INICIALIZACION

  ;Guarda en variables globales el numero de vertices y aristas, necesarios para la inicializacion del sistema.
  (bind ?*n-vertices* ?n-vertices)
  (bind ?*m-aristas* ?m-aristas)

  ;Guarda en una variable global el valor del techo del logaritmo en base 2 de m, necesario para la inicializacion del sistema.
  (bind ?log2-m (/ (log ?m-aristas) (log 2)))
  (bind ?*techo-log2-m* (techo ?log2-m))

  ;ESTRUCTURA DE MEMBRANAS

  (bind ?copias (integer (** 3 ?*n-vertices*))) ;Numero maximo de copias necesarias para determinados elementos en el entorno.

  (assert
    ;La membrana 0 representa al entorno (salida) y requiere ser inicializada con los elementos que codifican una instancia
    ; del problema 3-COL. Ademas contiene el resto de elementos necesarios para el sistema. [0 - {yes, no}]
    (membrana (etiqueta 0)
              (identificador 0)
              (contenido , 1 b , 1 D , ?copias E , ?copias e , ?copias T , 1 S , 1 N , ?copias z ,))

    (membrana (etiqueta 1) ;El estado inicial de la membrana 1 es igual para cualquier instancia del problema.
              (identificador 1)
              (contenido , 1 a 1 , 1 b , 1 c 1 , 1 yes , 1 no ,))

    ;La membrana 2 contiene, entre otros, los elementos de entrada que codifican una instancia del problema 3-COL. Por tanto
    ; tambien requiere ser inicializada con dichos elementos.
    (membrana (etiqueta 2)
              (identificador 2)
              (contenido , 1 D ,)))


  ;INSTANCIAS DE LAS REGLAS

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

  (bind ?k (integer (** 3 ?*n-vertices*))) ;COPIAS EN EL ENTORNO

  (modify ?entorno (contenido $?c0 ?k A ?i , ?k R ?i , ?k T ?i , ?k B ?i , ?k G ?i , ?k RC ?i , ?k BC ?i , ?k GC ?i ,))
  (modify ?entrada (contenido $?c2 1 A ?i ,))

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

  (bind ?k (integer (** 3 ?*n-vertices*))) ;COPIAS EN EL ENTORNO

  (modify ?entorno (contenido $?c0 ?k P ?i ?j , ?k PC ?i ?j , ?k R ?i ?j , ?k B ?i ?j , ?k G ?i ?j ,))
  (modify ?entrada (contenido $?c2 1 A ?i ?j ,))

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
             (bind ?contadores (create$ 1 ?tipo ?indice-a ,))
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
                (bind ?contadores (insert$ ?contadores 1 1 ?tipo ?indice-a ,))))

      (case c ;1 ... 2n + 1
        then (bind ?indice-c 1)
             (bind ?contadores (create$ 1 ?tipo ?indice-c ,))
             (bind ?copias 2) ;Copias necesarias del contador con el indice siguiente.
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
                (bind ?contadores (insert$ ?contadores 1 ?copias ?tipo ?indice-c ,))
                (bind ?copias (* ?copias 2))))

      (case d ;1 ... [log2(m)] + 1
        then (bind ?indice-d 1)
             (bind ?copias (integer (** 3 ?*n-vertices*)))
             (bind ?contadores (create$ ?copias ?tipo ?indice-d ,))
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
                (bind ?copias (* ?copias 2))
                (bind ?contadores (insert$ ?contadores 1 ?copias ?tipo ?indice-d ,))))

      (case f ;2 ... [log2(m)] + 7
        then (bind ?indice-f 2)
             (bind ?copias (integer (** 3 ?*n-vertices*)))
             (bind ?contadores (create$ ?copias ?tipo ?indice-f ,))
             (bind ?limite-f (+ ?*techo-log2-m* 7))
             (while (< ?indice-f ?limite-f)

                ;Regla asociada al contador f con indice i
                ;REGLA DE COMUNICACION (2 <-> 0)
                (assert (regla-comunicacion (etiqueta-izquierda 2) ;r9i
                                           (elemento1-izquierda f ?indice-f)
                                           (etiqueta-derecha 0)
                                           (elemento1-derecha f (+ ?indice-f 1))))

                (bind ?indice-f (+ ?indice-f 1))
                (bind ?contadores (insert$ ?contadores 1 ?copias ?tipo ?indice-f ,)))))

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

(defrule finaliza-computacion "termina la computacion si se ha llegado a una configuracion de parada"

  ?estado <- (estado actualizacion)

  (membrana (etiqueta 0)
            (contenido $? , ? yes|no , $?))

  =>
  (retract ?estado)
  (assert (estado respuesta))

)

;DIVISION

;Si se aplica una regla de division, en el mismo paso de la transicion no podra aplicarse ninguna otra regla ya sea
; de division o de comunicacion. Este hecho se controla de manera que al aplicar la regla de division se eliminan las membranas
; con configuracion actual por lo que no podra volverse a interactuar con ella hasta el siguiente paso de la transicion.

(defrule division "crea dos nuevas membranas en sustitucion de una existente y a partir de una regla de division concreta"

  ;Estado actual del sistema
  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ;Selecciona los elementos que definen la regla de division
  (regla-division (etiqueta ?etiqueta&~0&~1)
                  (elemento-izquierda $?elemento-izquierda)
                  (elemento1-derecha $?elemento1-derecha)
                  (elemento2-derecha $?elemento2-derecha))

  ?actual <- (membrana (etiqueta ?etiqueta)
                       (identificador ?id)
                       (configuracion ?pactual)
                       (contenido $? , ? $?elemento-izquierda , $?))

  ?siguiente <- (membrana (identificador ?id)
                          (configuracion ?psiguiente)
                          (contenido $?ci , ? $?elemento-izquierda , $?cf))

  =>
  (retract ?actual ?siguiente)

  (assert (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 1))
                    (configuracion ?psiguiente)
                    (contenido $?ci , 1 $?elemento1-derecha , $?cf))

          (membrana (etiqueta ?etiqueta)
                    (identificador (+ ?*id* 2))
                    (configuracion ?psiguiente)
                    (contenido $?ci , 1 $?elemento2-derecha , $?cf)))

  ;Incrementa el valor referencia del identificador de membranas.
  (bind ?*id* (+ ?*id* 2))

)

;COMUNICACION

;En un paso de la transicion pueden aplicarse varias reglas de comunicacion en caso de que en la membrana existan elementos que activen
; dichas reglas. Los elementos obtenidos de la aplicacion de una regla no se tienen en cuenta para la activacion de reglas hasta el
; siguiente paso. La longitud maxima de una regla es de cuatro, es decir, como maximo se envian dos elementos desde ambas membranas
; involucradas en la comunicacion.

(defrule comunicacion

  ;Estado actual del sistema
  (estado transicion)

  (paso-actual ?pactual)
  (paso-siguiente ?psiguiente)

  ;Regla que especifica la comunicacion a realizar.
  (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
                      (elemento1-izquierda $?elemento1-izquierda) ;Este elemento nunca puede ser vacio.
                      (elemento2-izquierda $?elemento2-izquierda)
                      (etiqueta-derecha ?etiqueta-derecha)
                      (elemento1-derecha $?elemento1-derecha) ;Si este elemento es vacio el segundo tambien lo es.
                      (elemento2-derecha $?elemento2-derecha))

  ;PARTE IZQUIERDA DE LA REGLA
  ?mi-actual <- (membrana (etiqueta ?etiqueta-izquierda)
                          (identificador ?id-izquierda)
                          (configuracion ?pactual)
                          (contenido $?ca-izquierda))

  ?mi-siguiente <- (membrana (etiqueta ?etiqueta-izquierda)
                             (identificador ?id-izquierda)
                             (configuracion ?psiguiente)
                             (contenido $?cs-izquierda))

  ;Comprueba si existen los elementos necesarios en la membrana especificada en la parte izquierda de la regla.

  (or ;ENVIA DOS ELEMENTOS IGUALES
    (and (test (eq $?elemento1-izquierda $?elemento2-izquierda))
         (test (existe-elemento $?ca-izquierda 2 $?elemento1-izquierda))
         (test (existe-elemento $?cs-izquierda 2 $?elemento1-izquierda)))

      ;ENVIA DOS ELEMENTOS DISTINTOS
    (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
         (test (existe-elemento $?ca-izquierda 1 $?elemento1-izquierda))
         (test (existe-elemento $?cs-izquierda 1 $?elemento1-izquierda))
         (test (existe-elemento $?ca-izquierda 1 $?elemento2-izquierda))
         (test (existe-elemento $?cs-izquierda 1 $?elemento2-izquierda))))


  ;PARTE DERECHA DE LA REGLA
  ?md-actual <- (membrana (etiqueta ?etiqueta-derecha)
                          (identificador ?id-derecha)
                          (configuracion ?pactual)
                          (contenido $?ca-derecha))

  ?md-siguiente <- (membrana (etiqueta ?etiqueta-derecha)
                             (identificador ?id-derecha)
                             (configuracion ?psiguiente)
                             (contenido $?cs-derecha))

  ;Comprueba si existen los elementos necesarios en la membrana especificada en la parte derecha de la regla

  (or ;ENVIA DOS ELEMENTOS IGUALES
    (and (test (eq $?elemento1-derecha $?elemento2-derecha))
         (test (existe-elemento $?ca-derecha 2 $?elemento1-derecha))
         (test (existe-elemento $?cs-derecha 2 $?elemento1-derecha)))

      ;ENVIA DOS ELEMENTOS DISTINTOS
    (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
         (test (existe-elemento $?ca-izquierda 1 $?elemento1-izquierda))
         (test (existe-elemento $?cs-izquierda 1 $?elemento1-izquierda))
         (test (existe-elemento $?ca-izquierda 1 $?elemento2-izquierda))
         (test (existe-elemento $?cs-izquierda 1 $?elemento2-izquierda))))

  =>

  ;EMISION MEMBRANA IZQUIERDA
  (if (eq $?elemento1-izquierda $?elemento2-izquierda)
    then (bind ?contenido-mi-actual    (elimina-elementos $?ca-izquierda 2 $?elemento1-izquierda))
         (bind ?contenido-mi-siguiente (elimina-elementos $?cs-izquierda 2 $?elemento1-izquierda))

         (bind ?contenido-md-siguiente (agrega-elementos $cs-derecha 2 $?elemento1-izquierda))

    else (bind ?contenido-mi-actual    (elimina-elementos $?ca-izquierda 1 $?elemento1-izquierda))
         (bind ?contenido-mi-actual    (elimina-elementos ?contenido-mi-actual 1 $?elemento2-izquierda))
         (bind ?contenido-mi-siguiente (elimina-elementos $?cs-izquierda 1 $?elemento1-izquierda))
         (bind ?contenido-mi-siguiente (elimina-elementos ?contenido-mi-siguiente 1 $?elemento2-izquierda))

         (bind ?contenido-md-siguiente (agrega-elementos $?cs-derecha 1 $?elemento1-izquierda))
         (bind ?contenido-md-siguiente (agrega-elementos ?contenido-md-siguiente 1 $?elemento2-izquierda)))

 ;EMISION MEMBRANA DERECHA
 (if (eq $?elemento1-derecha $?elemento2-derecha)
   then (bind ?contenido-md-actual    (elimina-elementos $?ca-derecha 2 $?elemento1-derecha))
        (bind ?contenido-md-siguiente (elimina-elementos ?contenido-md-siguiente 2 $?elemento1-derecha))

        (bind ?contenido-mi-siguiente (agrega-elementos ?contenido-mi-siguiente 2 $?elemento2-derecha))

   else (bind ?contenido-md-actual    (elimina-elementos $?ca-derecha 1 $?elemento1-derecha))
        (bind ?contenido-md-actual    (elimina-elementos ?contenido-md-actual 1 $?elemento2-derecha))
        (bind ?contenido-md-siguiente (elimina-elementos $?cs-derecha 1 $?elemento1-derecha))
        (bind ?contenido-md-siguiente (elimina-elementos ?contenido-md-siguiente 1 $?elemento2-derecha))

        (bind ?contenido-mi-siguiente (agrega-elementos ?contenido-mi-siguiente 1 $?elemento1-derecha))
        (bind ?contenido-mi-siguiente (agrega-elementos ?contenido-mi-siguiente 1 $?elemento2-derecha)))

  ;Modifica el contenido de cada membrana producto de la comunicacion.
  (modify ?mi-actual    (contenido ?contenido-mi-actual))
  (modify ?mi-siguiente (contenido ?contenido-mi-siguiente))
  (modify ?md-actual    (contenido ?contenido-md-actual))
  (modify ?md-siguiente (contenido ?contenido-md-siguiente))

)

; (defrule comunicacion-symport-1 "modela la comunicacion tipo symport en la que se envia un unico elemento"
;
;   ;Estado actual del sistema
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ;Regla que especifica la comunicacion a realizar.
;   (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                       (elemento1-izquierda $?elemento1-izquierda)
;                       (elemento2-izquierda)
;                       (etiqueta-derecha ?etiqueta-derecha)
;                       (elemento1-derecha)
;                       (elemento2-derecha))
;
;   ;El elemento a enviar se encuentra en la membrana emisora con configuracion actual y siguiente.
;   (membrana (etiqueta ?etiqueta-izquierda)
;             (identificador ?id-izquierda)
;             (configuracion ?pactual)
;             (contenido $?cei1 , ? $?elemento1-izquierda , $?cef1))
;
;   (membrana (identificador ?id-izquierda)
;             (configuracion ?psiguiente)
;             (contenido $?cei2 , ? ?$?elemento1-izquierda , $?cef2))
;
;   ;Receptora.
;   (membrana (etiqueta ?etiqueta-derecha)
;             (identificador ?id-derecha))
;
;   =>
;   ;Incluye en la memoria de trabajo un hecho para llevar a cabo el envio de los elementos entre las membranas.
;   (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                           (identificador-receptor ?id-derecha)
;                           (elemento-enviado 1 $?elemento1-izquierda)))
;
; )
;
; (defrule comunicacion-symport-2 "modela la comunicacion tipo symport en la que se envian dos elementos"
;
;   ;Estado actual del sistema
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ;Regla que especifica la comunicacion a realizar.
;   (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                       (elemento1-izquierda $?elemento1-izquierda)
;                       (elemento2-izquierda $?elemento2-izquierda)
;                       (etiqueta-derecha ?etiqueta-derecha)
;                       (elemento1-derecha)
;                       (elemento2-derecha))
;
;   ;Los elementos a enviar se encuentran en la membrana emisora con configuracion actual y siguiente.
;
;   (or
;
;     ;ENVIA DOS ELEMENTOS IGUALES
;     (and (test (eq $?elemento1-izquierda $?elemento2-izquierda))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ?k&:(>= ?k 2) $?elemento1-izquierda , $?))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ?k $?elemento1-izquierda , $?)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento1-izquierda , $?))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento1-izquierda , $?))
;
;
;          (membrana (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento2-izquierda , $?))
;
;          (membrana (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento2-izquierda , $?))))
;
;   ;Receptora
;   (membrana (etiqueta ?etiqueta-derecha)
;             (identificador ?id-derecha))
;
;   =>
;   ;Incluye en la memoria de trabajo el/los hecho/s para llevar a cabo el envio de los elementos entre membranas.
;   (if (eq $?elemento1-izquierda $?elemento2-izquierda)
;
;     ;ENVIA DOS ELEMENTOS IGUALES
;     then (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 2 $?elemento1-izquierda)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     else (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 1 $?elemento1-izquierda))
;
;                  (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 1 $?elemento2-izquierda))))
;
; )
;
; (defrule comunicacion-antiport-1 "modela la comunicacion tipo antiport en la que se envia y se recibe un elemento"
;
;   ;Estado actual del sistema
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ;Regla que especifica la comunicacion a realizar. (ANTIPORT 1 <-> 1)
;   (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                       (elemento1-izquierda $?elemento1-izquierda)
;                       (elemento2-izquierda)
;                       (etiqueta-derecha ?etiqueta-derecha)
;                       (elemento1-derecha $?elemento1-derecha)
;                       (elemento2-derecha))
;
;   ;El elemento a enviar se encuentra en la membrana emisora con configuracion actual y siguiente.
;
;   ;PARTE IZQUIERDA DE LA REGLA
;   (membrana (etiqueta ?etiqueta-izquierda)
;             (identificador ?id-izquierda)
;             (configuracion ?pactual)
;             (contenido $? , ? $?elemento1-izquierda , $?))
;
;   (membrana (identificador ?id-izquierda)
;             (configuracion ?psiguiente)
;             (contenido $? , ? $?elemento1-izquierda , $?))
;
;   ;PARTE DERECHA DE LA REGLA
;   (membrana (etiqueta ?etiqueta-derecha)
;             (identificador ?id-derecha)
;             (configuracion ?pactual)
;             (contenido $? , ? $?elemento1-derecha , $?))
;
;   (membrana (identificador ?id-derecha)
;             (configuracion ?psiguiente)
;             (contenido $? , ? $?elemento1-derecha , $?))
;
;   =>
;   ;Incluye en la memoria de trabajo los hechos para llevar a cabo el envio de los elementos entre membranas.
;   (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                           (identificador-receptor ?id-derecha)
;                           (elemento-enviado 1 $?elemento1-izquierda))
;
;           (envia-elemento (identificador-emisor ?id-derecha)
;                           (identificador-receptor ?id-izquierda)
;                           (elemento-enviado 1 $?elemento1-derecha)))
;
; )
;
; (defrule comunicacion-antiport-2 "modela la comunicacion tipo antiport en la que se envia un elemento y se reciben dos"
;
;   ;Estado actual del sistema
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ;Regla que especifica la comunicacion a realizar. (ANTIPORT 1 <-> 2)
;   (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                       (elemento1-izquierda $?elemento1-izquierda)
;                       (elemento2-izquierda)
;                       (etiqueta-derecha ?etiqueta-derecha)
;                       (elemento1-derecha $?elemento1-derecha)
;                       (elemento2-derecha $?elemento2-derecha))
;
;   ;El elemento a enviar se encuentra en la membrana emisora con configuracion actual y siguiente.
;
;   ;PARTE IZQUIERDA DE LA REGLA
;   (membrana (etiqueta ?etiqueta-izquierda)
;             (identificador ?id-izquierda)
;             (configuracion ?pactual)
;             (contenido $? , ? $?elemento1-izquierda , $?))
;
;   (membrana (identificador ?id-izquierda)
;             (configuracion ?psiguiente)
;             (contenido $? , ? $?elemento1-izquierda , $?))
;
;   ;PARTE DERECHA DE LA REGLA
;   (or
;     ;ENVIA DOS ELEMENTOS IGUALES
;     (and (test (eq $?elemento1-derecha $?elemento2-derecha))
;
;          (membrana (etiqueta ?etiqueta-derecha)
;                    (identificador ?id-derecha)
;                    (configuracion ?pactual)
;                    (contenido $? , ?k&:(>= ?k 2) $?elemento1-derecha , $?))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ?k $?elemento1-derecha , $?)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     (and (test (neq $?elemento1-derecha $?elemento2-derecha))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento1-derecha , $?))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento1-derecha , $?))
;
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento2-derecha , $?))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento2-derecha , $?))))
;
;   =>
;   ;Incluye en la memoria de trabajo los hechos para llevar a cabo el envio de los elementos entre membranas.
;   (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                           (identificador-receptor ?id-derecha)
;                           (elemento-enviado 1 $?elemento1-izquierda)))
;
;   (if (eq $?elemento1-derecha $?elemento2-derecha)
;
;     ;ENVIA DOS ELEMENTOS IGUALES
;     then (assert (envia-elemento (identificador-emisor ?id-derecha)
;                                  (identificador-receptor ?id-izquierda)
;                                  (elemento-enviado 2 $?elemento1-derecha)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     else (assert (envia-elemento (identificador-emisor ?id-derecha)
;                                  (identificador-receptor ?id-izquierda)
;                                  (elemento-enviado 1 $?elemento1-derecha))
;
;                  (envia-elemento (identificador-emisor ?id-derecha)
;                                  (identificador-receptor ?id-izquierda)
;                                  (elemento-enviado 1 $?elemento2-derecha))))
;
; )
;
; (defrule comunicacion-antiport-3 "modela la comunicacion tipo antiport en la que se envian dos elemento y se recibe uno"
;
;   ;Estado actual del sistema
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ;Regla que especifica la comunicacion a realizar. (ANTIPORT 2 <-> 1)
;   (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                       (elemento1-izquierda $?elemento1-izquierda)
;                       (elemento2-izquierda $?elemento2-izquierda)
;                       (etiqueta-derecha ?etiqueta-derecha)
;                       (elemento1-derecha $?elemento1-derecha)
;                       (elemento2-derecha))
;
;   ;El elemento a enviar se encuentra en la membrana emisora con configuracion actual y siguiente.
;
;   ;PARTE IZQUIERDA DE LA REGLA
;   (or
;     ;ENVIA DOS ELEMENTOS IGUALES
;     (and (test (eq $?elemento1-izquierda $?elemento2-izquierda))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ?k&:(>= ?k 2) $?elemento1-izquierda , $?))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ?k $?elemento1-izquierda , $?)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento1-izquierda , $?))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento1-izquierda , $?))
;
;
;          (membrana (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento2-izquierda , $?))
;
;          (membrana (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento2-izquierda , $?))))
;
;
;   ;PARTE DERECHA DE LA REGLA
;   (membrana (etiqueta ?etiqueta-derecha)
;             (identificador ?id-derecha)
;             (configuracion ?pactual)
;             (contenido $? , ? $?elemento1-derecha , $?))
;
;   (membrana (identificador ?id-derecha)
;             (configuracion ?psiguiente)
;             (contenido $? , ? $?elemento1-derecha , $?))
;
;   =>
;   ;Incluye en la memoria de trabajo el/los hecho/s para llevar a cabo el envio de los elementos entre membranas.
;   (if (eq $?elemento1-izquierda $elemento2-izquierda)
;
;     ;ENVIA DOS ELEMENTOS IGUALES
;     then (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 2 $?elemento1-izquierda)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     else (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 1 $?elemento1-izquierda))
;
;                  (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 1 $?elemento2-izquierda))))
;
;     (assert (envia-elemento (identificador-emisor ?id-derecha)
;                             (identificador-receptor ?id-izquierda)
;                             (elemento-enviado 1 $?elemento1-derecha)))
;
; )
;
; (defrule comunicacion-antiport-4 "modela la comunicacion tipo antiport en la que se envian dos elemento y se reciben otros dos"
;   ;Estado actual del sistema
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ;Regla que especifica la comunicacion a realizar. (ANTIPORT 2 <-> 2)
;   (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                       (elemento1-izquierda $?elemento1-izquierda)
;                       (elemento2-izquierda $?elemento2-izquierda)
;                       (etiqueta-derecha ?etiqueta-derecha)
;                       (elemento1-derecha $?elemento1-derecha)
;                       (elemento2-derecha $?elemento2-derecha))
;
;   (test (> (length $?elemento1-izquierda) 0))
;   (test (> (length $?elemento2-izquierda) 0))
;   (test (> (length $?elemento1-derecha) 0))
;   (test (> (length $?elemento2-derecha) 0))
;
;   ;El elemento a enviar se encuentra en la membrana emisora con configuracion actual y siguiente.
;
;   ;PARTE IZQUIERDA DE LA REGLA
;   (or
;     ;ENVIA DOS ELEMENTOS IGUALES
;     (and (test (eq $?elemento1-izquierda $?elemento2-izquierda))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ?k&:(>= ?k 2) $?elemento1-izquierda , $?))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ?k $?elemento1-izquierda , $?)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     (and (test (neq $?elemento1-izquierda $?elemento2-izquierda))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento1-izquierda , $?))
;
;          (membrana (etiqueta ?etiqueta-izquierda)
;                    (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento1-izquierda , $?))
;
;
;          (membrana (identificador ?id-izquierda)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento2-izquierda , $?))
;
;          (membrana (identificador ?id-izquierda)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento2-izquierda , $?))))
;
;
;   ;PARTE DERECHA DE LA REGLA
;   (or
;     ;ENVIA DOS ELEMENTOS IGUALES
;     (and (test (eq $?elemento1-derecha $?elemento2-derecha))
;
;          (membrana (etiqueta ?etiqueta-derecha)
;                    (identificador ?id-derecha)
;                    (configuracion ?pactual)
;                    (contenido $? , ?k&:(>= ?k 2) $?elemento1-derecha , $?))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ?k $?elemento1-derecha , $?)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     (and (test (neq $?elemento1-derecha $?elemento2-derecha))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento1-derecha , $?))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento1-derecha , $?))
;
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?pactual)
;                    (contenido $? , ? $?elemento2-derecha , $?))
;
;          (membrana (identificador ?id-derecha)
;                    (configuracion ?psiguiente)
;                    (contenido $? , ? $?elemento2-derecha , $?))))
;
;   =>
;   ;Incluye en la memoria de trabajo el/los hecho/s para llevar a cabo el envio de los elementos entre membranas.
;
;   ;PARTE IZQUIERDA DE LA REGLA
;   (if (eq $?elemento1-izquierda $elemento2-izquierda)
;
;     ;ENVIA DOS ELEMENTOS IGUALES
;     then (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 2 $?elemento1-izquierda)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     else (assert (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 1 $?elemento1-izquierda))
;
;                  (envia-elemento (identificador-emisor ?id-izquierda)
;                                  (identificador-receptor ?id-derecha)
;                                  (elemento-enviado 1 $?elemento2-izquierda))))
;
;   ;PARTE DERECHA DE LA REGLA
;   (if (eq $?elemento1-derecha $?elemento2-derecha)
;
;     ;ENVIA DOS ELEMENTOS IGUALES
;     then (assert (envia-elemento (identificador-emisor ?id-derecha)
;                                  (identificador-receptor ?id-izquierda)
;                                  (elemento-enviado 2 $?elemento1-derecha)))
;
;     ;ENVIA DOS ELEMENTOS DISTINTOS
;     else (assert (envia-elemento (identificador-emisor ?id-derecha)
;                                  (identificador-receptor ?id-izquierda)
;                                  (elemento-enviado 1 $?elemento1-derecha))
;
;                  (envia-elemento (identificador-emisor ?id-derecha)
;                                  (identificador-receptor ?id-izquierda)
;                                  (elemento-enviado 1 $?elemento2-derecha))))
;
; )
;
; ;Antes de aplicar alguna otra regla nueva, ya sea de comunicacion o division, hay que realizar los envios pendientes
; ; de la regla de comunicacion recien disparada y que ha generado la activacion de esta regla.
;
; (defrule realiza-envio "envia, de una membrana a otra, los elementos determinados por una regla de comunicacion concreta"
;   (declare (salience 96))
;
;   (estado transicion)
;
;   (paso-actual ?pactual)
;   (paso-siguiente ?psiguiente)
;
;   ?envio <- (envia-elemento (identificador-emisor ?id-emisor)
;                             (identificador-receptor ?id-receptor)
;                             (elemento-enviado ?copias $?elemento))
;
;   ?emisora-actual  <- (membrana (identificador ?id-emisor)
;                                 (configuracion ?pactual)
;                                 (contenido $?cea))
;
;   ?emisora-siguiente  <- (membrana (identificador ?id-emisor)
;                                    (configuracion ?psiguiente)
;                                    (contenido $?ces))
;
;   ?receptora <- (membrana (identificador ?id-receptor)
;                           (configuracion ?psiguiente)
;                           (contenido $?cr))
;
;   =>
;   (retract ?envio)
;
;   ;Elimina elementos de la membrana emisora
;   (bind ?contenido-emisora-actual    (elimina-elementos $?cea ?copias $?elemento))
;   (bind ?contenido-emisora-siguiente (elimina-elementos $?ces ?copias $?elemento))
;
;   (modify ?emisora-actual   (contenido ?contenido-emisora-actual))
;   (modify ?emisora-siguiente (contenido ?contenido-emisora-siguiente))
;
;   ;Incluye elementos en la membrana receptora
;   (bind ?contenido-receptora (agrega-elementos $?cr ?copias $?elemento))
;
;   (modify ?receptora (contenido ?contenido-receptora))
;
; )

; (defrule finaliza-transicion "comprueba si queda alguna regla de comunicacion por aplicar en la configuracion actual"
;
;   ?estado <- (estado transicion)
;
;   (paso-actual ?pactual)
;
;   ;Comprueba que no queda ninguna regla de comunicacion que se pueda aplicar.
;   (not
;     (and
;       (regla-comunicacion (etiqueta-izquierda ?etiqueta-izquierda)
;                           (elemento1-izquierda $?elemento1-izquierda) ;Siempre hay un valor
;                           (elemento2-izquierda $?elemento2-izquierda) ;Puede ser vacio
;                           (etiqueta-derecha ?etiqueta-derecha)
;                           (elemento1-derecha $?elemento1-derecha)     ;Puede ser vacio
;                           (elemento2-derecha $?elemento2-derecha))    ;Puede ser vacio
;
;       (or ;PARTE IZQUIERDA DE LA REGLA.
;           ;La membrana especificada en la parte izquierda de la regla envia 1 elemento. (Antiport)
;           (and (test (= (length $?elemento2-izquierda) 0))
;
;                (membrana (etiqueta ?etiqueta-izquierda)
;                          (configuracion ?pactual)
;                          (contenido $?, $?elemento1-izquierda , $?)))
;
;           ;La membrana especificada en la parte izquierda de la regla envia 2 elementos. (Antiport)
;           (and (test (<> (length $?elemento2-izquierda) 0))
;               (membrana (etiqueta ?etiqueta-izquierda)
;                          (identificador ?id-izquierda)
;                          (configuracion ?pactual)
;                          (contenido $?cii1 , $?elemento1-izquierda , $?cii2))
;
;                (membrana (etiqueta ?etiqueta-izquierda)
;                          (identificador ?id-izquierda)
;                          (configuracion ?pactual)
;                          (contenido $?cif1 , $?elemento2-izquierda , $?cif2))
;
;                          (test (neq $?cii1 $?cii2))
;                          (test (neq $?cif1 $?cif2))))
;
;       (or ;PARTE DERECHA DE LA REGLA.
;           ;Se trata de una comunicacion con el entorno.
;           (and
;             (test (= ?etiqueta-derecha 0))
;
;             (membrana (etiqueta 0)
;                       (configuracion ?pactual)))
;
;           ;La membrana especificada en la parte derecha de la regla no envia ningun elemento. (Symport)
;           (and
;             (test (= (length $?elemento1-derecha) 0)) ; Si el elemento 1 es vacio el segundo tambien lo es.
;
;             (membrana (etiqueta ?etiqueta-derecha)
;                       (configuracion ?pactual)))
;
;           (and ;La membrana especificada en la parte derecha de la regla envia 1 elemento. (Antiport)
;             (test (<> ?etiqueta-derecha 0))
;             (test (<> (length $?elemento1-derecha) 0))
;             (test (= (length $?elemento2-derecha) 0))
;
;             (membrana (etiqueta ?etiqueta-derecha)
;                       (configuracion ?pactual)
;                       (contenido $? , $?elemento1-derecha , $?)))
;
;           (and ;La membrana especificada en la parte derecha de la regla envia 2 elementos. (Antiport)
;             (test (<> ?etiqueta-derecha 0))
;             (test (<> (length $?elemento1-derecha) 0))
;             (test (<> (length $?elemento2-derecha) 0))
;
;             (membrana (etiqueta ?etiqueta-derecha)
;                       (identificador ?id-derecha)
;                       (configuracion ?pactual)
;                       (contenido $?cdi1 , $?elemento1-derecha , $?cdf1))
;
;             (membrana (etiqueta ?etiqueta-derecha)
;                       (identificador ?id-derecha)
;                       (configuracion ?pactual)
;                       (contenido $?cdi2 , $?elemento2-derecha , $?cdf2))
;
;             ;Comprueba que no selecciona el mismo elemento 2 veces en caso de que sean iguales.
;             (test (neq $?cdi1 $?cdi2))
;             (test (neq $?cdf1 $?cdf2))))))
;
;     =>
;     (retract ?estado)
;     (assert (estado actualizacion))
;
; )


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

  ;El sistema no se encuenta en la configuracion de parada.
  (not (membrana (etiqueta 0)
                 (contenido $? , yes|no , $?)))

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
