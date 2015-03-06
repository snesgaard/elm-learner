import Color (..)
import Debug
import Graphics.Collage (..)
import Graphics.Element (..)
import List
import Maybe
import Mouse
import Signal
import Signal (Signal)
import Text
import Time
import Window


type alias Point2i = (Int, Int)
type alias Point2f = (Float, Float)

pointi2f : Point2i -> Point2f
pointi2f (x, y) = (toFloat x, toFloat y)

subPoint2f : Point2f -> Point2f -> Point2f
subPoint2f (x1, y1) (x2, y2) = (x1 - x2, y1 - y2)

sqLengthPoint2f : Point2f -> Float
sqLengthPoint2f (x, y) = x * x + y * y

lengthPoint2f : Point2f -> Float
lengthPoint2f (x, y) = sqrt(x * x + y * y)

unit : Point2f -> Point2f
unit (x, y) =
  let l = lengthPoint2f (x, y)
  in if | l == 0 -> (x, y)
        | otherwise -> (x / l, y / l)

addPoint2f : Point2f -> Point2f -> Point2f
addPoint2f (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)

divPoint2f : Float -> Point2f -> Point2f
divPoint2f s (x, y) = (x / s, y / s)

mulPoint2f : Float -> Point2f -> Point2f
mulPoint2f s (x, y) = (x * s, y * s)

dot : Point2f -> Point2f -> Float
dot (x1, y1) (x2, y2) = x1 * x2 + y1 * y2

cross : Point2f -> Point2f -> Float
cross (x1, y1) (x2, y2) = x1 * y2 - x2 * y1

rotate90 : Point2f -> Point2f
rotate90 (x, y) = (-y, x)

signalSwitch : Bool -> a -> Maybe a
signalSwitch s i =
  if | s -> Just i
     | otherwise -> Nothing

maybeMap2 : (a -> b -> c) -> Maybe a -> Maybe b -> Maybe c
maybeMap2 f ma mb =
  case ma of
    Nothing -> Nothing
    Just va -> case mb of
      Nothing -> Nothing
      Just vb -> Just <| f va vb

zip : List a -> List b -> List (a, b)
zip la lb =
  if | ((List.length la == 0) || (List.length lb == 0)) -> []
     | otherwise ->
     let ha = List.head la
         hb = List.head lb
     in (ha, hb) :: (zip (List.tail la) (List.tail lb))

isNothing : Maybe a -> Bool
isNothing m =
  case m of
    Nothing -> True
    Just _ -> False

isJust : Maybe a -> Bool
isJust = not << isNothing

type alias UserInput = { click : Maybe Point2i, win : (Int, Int) }
userInput : Signal UserInput
userInput =
  let c = Signal.map2 signalSwitch Mouse.isDown Mouse.position
  in Signal.map2 UserInput c Window.dimensions
type alias Input =
  { timeDelta : Float
  , userInput : UserInput
  }

type alias Ball = { center : Point2f, radius : Float, velocity : Point2f }
unitBall : Ball
unitBall = Ball (0, 0) 1 (0, 0)

type alias BarrierTrail = { vertex : List Point2f, normals : List Point2f}
emptyBarrierTrail : BarrierTrail
emptyBarrierTrail = BarrierTrail [] []

toBarrierTrail : List Point2f -> BarrierTrail
toBarrierTrail lp = BarrierTrail lp (findNormals lp)

type alias GameState = { ball : Ball, barriers : List BarrierTrail,
                          wipBarrier : Maybe BarrierTrail }
defaultGame : GameState
defaultGame = GameState (Ball (100,100) 40 (0.5,0.5)) [] Nothing

findNormals : List Point2f -> List Point2f
findNormals vertices =
  let s = List.map2 subPoint2f (List.tail vertices) vertices
  in List.map (unit << rotate90) s

removeDuplicates : Float -> List Point2f -> List Point2f
removeDuplicates m lp =
  if | List.length lp < 2 -> lp
     | otherwise ->
       let p1 = List.head lp
           p2 = List.head <| List.tail lp
           r = List.tail <| List.tail lp
           d = lengthPoint2f <| subPoint2f p1 p2
       in if | d < m -> (p1 :: removeDuplicates m r)
             | otherwise -> (p1 :: p2 :: removeDuplicates m r)

limitLength : Float -> List Point2f -> List Point2f
limitLength l lp =
  if | List.length lp < 2 -> lp
     | otherwise ->
       let p1 = List.head lp
           r = List.tail lp
           p2 = List.head <| r
           d = lengthPoint2f <| subPoint2f p1 p2
       in if | d > l -> [p1]
             | otherwise -> (p1 :: limitLength (l - d) r)

addPointBarrier : BarrierTrail -> Point2i -> BarrierTrail
addPointBarrier b ip =
  let maxv = 800
      p = pointi2f ip
      --addAndCull = List.append [p] << List.take (maxv - 1)
      addAndCull = (limitLength maxv) << (removeDuplicates 1) << List.append [p]
      v = addAndCull b.vertex
      n = findNormals v
  in BarrierTrail v n

stepBarrier : List BarrierTrail -> Maybe Point2i -> Maybe BarrierTrail -> List BarrierTrail
stepBarrier bl mp mb =
  case mp of
    Just p -> bl
    Nothing ->
      let nbl = Maybe.map (\nb -> nb :: bl) mb
      in Maybe.withDefault bl nbl

-- Returns the initial time of impatch between a line and a sphere
-- Nothing if there is no possible contact
ballLineSweep : Ball -> Point2f -> Point2f -> Maybe Float
ballLineSweep ball p1 p2 =
  let v = ball.velocity
      cen = ball.center
      r = ball.radius
      dp = subPoint2f p2 p1
      f = subPoint2f p1 cen
      a = 4 * ((dot v dp) ^ 2 - (dot dp dp) * (dot v v))
      b = 8 * ( (dot dp dp) * (dot f v) - (dot f dp) * (dot v dp)) / a
      c = 4 * ((dot f dp) ^ 2 - (dot dp dp) * (dot f f) - (dot dp dp) * r ^ 2) / a
      d = b ^ 2 - 4 * c
  in if | d < 0 -> Nothing
        | otherwise ->
          let sqd = sqrt(d)
          in Just <| min ((-b + sqd) * 0.5 / a) ((-b - sqd) * 0.5 / a)

type alias Circle = { radius : Float, center : Point2f}
type alias Line = {start : Point2f, end : Point2f}


quadraticSolve : Float -> Float -> Float -> Maybe (Float, Float)
quadraticSolve a b c =
  let d = b ^ 2 - 4 * a * c
      t = 1e-10
  in if | d < 0 || abs(a) < t -> Nothing
        | otherwise ->
          let sqd = sqrt(d)
          in Just ((-b - d) * 0.5 / a, (-b + d) * 0.5 / a)

lineLineIntersection : Line -> Line -> Maybe Point2f
lineLineIntersection l1 l2 =
  let p = l1.start
      q = l2.start
      r = subPoint2f l1.end p
      s = subPoint2f l2.end q
      rxs = cross r s
      tol = 1e-10
  in if | abs(rxs) < tol -> Nothing
        | otherwise ->
          let t = (cross (subPoint2f q p) s) / rxs
              u = (cross (subPoint2f q p) r) / rxs
              g = (\c -> 0 <= c && c <= 1)
          in if | not <| (g t) && (g u) -> Nothing
                | otherwise -> Just <| addPoint2f p <| mulPoint2f t r

type CircleLineIntersection =
  NoIntersection
  | SingleIntersection (Float)
  | DoubleIntersection (Float, Float)

circleLineIntersection : Circle -> Line -> CircleLineIntersection
circleLineIntersection cir l =
  let p1 = l.start
      p2 = l.end
      cen = cir.center
      r = cir.radius
      d = subPoint2f p2 p1
      f = subPoint2f p1 cen
      a = dot d d
      b = 2 * dot d f
      c = r ^ 2 + (dot f f)
      tol = 1e-10
  in if | abs(a) < tol -> NoIntersection
        | otherwise ->
          let ms = quadraticSolve 1 (b / a) (c / a)
              f = (\t -> addPoint2f <| mulPoint2f t d)
          in case ms of
            Nothing -> NoIntersection
            Just (t1, t2) ->
              let g = (\t -> t >= 0 && t <= 1)
              in if | (g t1) && (g t2) -> DoubleIntersection (t1, t2)
                    | g t1 -> SingleIntersection t1
                    | g t2 -> SingleIntersection t2
                    | otherwise -> NoIntersection


-- Function that takes a normal and velocity and returns velocity with
-- reverse momentum along said normal.
reverseMomentum : Point2f -> Point2f -> Point2f
reverseMomentum n v =
  let i = dot n v
  in subPoint2f v <| mulPoint2f (2 * i) n

type alias Collision =  (Float, Point2f)

-- Ball to barrier collision detection,
-- Returns the nearest collision, if any.
ballBarrierCD : Float -> Ball -> BarrierTrail -> Maybe Collision
ballBarrierCD t ball barrier =
  let v = barrier.vertex
      norm = barrier.normals
      vel = mulPoint2f t ball.velocity
      utraj = unit vel
      r = ball.radius
      cen = addPoint2f ball.center <| mulPoint2f r utraj
      traj = Line cen (addPoint2f cen <| vel)
      lines = List.map2 Line v (List.tail v)
      msecline = List.map (lineLineIntersection traj) lines
      normalfilter = List.map (\(n, p) -> (n, Maybe.withDefault (0,0) p))
                      << List.filter (\(n, p) -> isJust p) << zip norm
      secnorm = normalfilter msecline
  in if | (List.length secnorm) == 0 -> Nothing
        | otherwise ->
          let scaleproj = (\a b  -> (dot a b) / (dot b b))
              (rnorm, rcontact) = List.unzip secnorm
              timemap = (\p -> t * (scaleproj (subPoint2f p cen) vel))
              rtime = List.map timemap rcontact
              normtime = zip rtime rnorm
              _ = Debug.watch "normtime" (normtime, traj)
          in Just <| List.head <| List.sortBy (\(dt, n) -> dt) normtime


stepBall : Float -> List BarrierTrail -> Ball -> Ball
stepBall t lb b =
  let tol = 1e-10
  in if | t < tol -> b
        | otherwise ->
          let c = b.center
              v = b.velocity
              --_ = Debug.watch "v" v
              mlcol = List.map (ballBarrierCD t b) lb
              --_ = Debug.watch "lb" lb
              lcol = List.map (Maybe.withDefault (t + 1, (0, 0))) mlcol
              sortlcol = List.sortBy (\(c, n) -> c) <| List.filter (\(c, n) -> c < t) lcol
          in if | List.length sortlcol == 0 ->  {b | center <- addPoint2f c <| mulPoint2f t v}
                | otherwise ->
                  let (t1, n) = List.head sortlcol
                      v1 = v
                      t2 = t - t1
                      v2 = reverseMomentum n v
                      d = mulPoint2f t1 v1
                      _ = Debug.watch "boom" (t1, v1, t2, v2)
                      nb = {b | center <- addPoint2f c d,
                              velocity <- v2}
                  in stepBall t2 lb nb



stepGame : Input -> GameState -> GameState
stepGame {timeDelta,userInput} gameState =
  let mb = gameState.wipBarrier
      ip = userInput.click
      fip = addPointBarrier (Maybe.withDefault emptyBarrierTrail mb)
      nmb = Maybe.map fip ip
      bl = gameState.barriers
      nbs = stepBarrier bl ip mb
      -- Step ball
      (wx, wy) = pointi2f userInput.win
      border = toBarrierTrail [(0, 0), (wx, 0), (wx, wy), (0, wy), (0, 0)]
      b = stepBall timeDelta (border :: nbs) gameState.ball
  in { gameState | barriers <- nbs, wipBarrier <- nmb, ball <- b }
--  let b = gameState.barriers
--      mb = Maybe.map (updateBarrier b) userInput.click
--  in { gameState | barrier <- Maybe.withDefault b mb }

vertexNormals : List Point2f -> List Point2f
vertexNormals n =
  let n1 = List.append [(0, 0)] n
      n2 = List.append n [(0, 0)]
  in List.map unit (List.map2 addPoint2f n1 n2)

barrierPolygon : BarrierTrail -> List (Float, Float)
barrierPolygon b =
  let vn = List.map (mulPoint2f 5) (vertexNormals b.normals)
      pbp = List.map2 addPoint2f vn b.vertex
      nbp = List.map2 subPoint2f b.vertex vn
  in  List.append pbp (List.reverse nbp)

mouse2Field : (Int, Int) -> (Float, Float) -> (Float, Float)
mouse2Field (w, h) (x, y) =
  let (hw, hh) = (toFloat <| w // 2, toFloat <| h // 2)
      screenCastX = (max (-hw)) << (min hw)
      screenCastY = (max (-hh)) << (min hh)
  in (screenCastX (x - hw), screenCastX (-y + hh))

display : (Int,Int) -> GameState -> Element
display (w,h) gameState =
  let m2f = mouse2Field (w, h)
      -- Render barriers and in progress barrier
      b2p = polygon << List.map m2f << barrierPolygon
      bpl = List.map (filled black << b2p) gameState.barriers
      wipb = Maybe.map (filled green << b2p) gameState.wipBarrier
      allb = Maybe.withDefault bpl <| Maybe.map (\b -> b :: bpl) wipb
      -- Render ball in the field
      b = gameState.ball
      bform = move (m2f b.center) <| filled black <| oval (2 * b.radius) (2 * b.radius)
      allform = bform :: allb
  in (container w h middle) <| (collage w h allform)

delta : Signal Float
delta =
  Time.fps 60
input : Signal Input
input =
  Signal.sampleOn delta (Signal.map2 Input delta userInput)
gameState : Signal GameState
gameState =
  Signal.foldp stepGame defaultGame input
main : Signal Element
main =
  Signal.map2 display Window.dimensions gameState
