-- Copyright 2014 2015 2016, Julia Longtin (julial@turinglace.com)
-- Copyright 2015 2016, Mike MacHenry (mike.machenry@gmail.com)
-- Implicit CAD. Copyright (C) 2011, Christopher Olah (chris@colah.ca)
-- Released under the GNU AGPLV3+, see LICENSE

module Graphics.Implicit.ObjectUtil.GetImplicit3 (getImplicit3) where

-- Import only what we need from the prelude.
import Prelude (abs, atan2, cos, ceiling, either, error, floor, fromInteger, id, max, min, minimum, negate, odd, otherwise, pi, pure, round, show, sin, sqrt, (||), (/=), Either(Left, Right), (<), (<=), (<>), (>), (>=), (&&), (-), (/), (*), (+), ($), (.), Bool(True, False), (==), (**), Num, Applicative, (<$>))

import Control.Lens ((^.))

import qualified Data.Either as Either (either)

import Data.List(genericIndex, length)

import Linear (V2(V2), V3(V3), _xy, _z, distance, dot)
import qualified Linear (conjugate, inv44, normalizePoint, normalize, point, rotate, Metric)

import Linear.V3 (cross)

-- Matrix times column vector.
import Linear.Matrix ((!*))

-- Matrix times scalar.
import Linear.Vector ((*^))

import Graphics.Implicit.Definitions
    ( objectRounding,
      ObjectContext,
      ℕ,
      SymbolicObj3(Cube, Sphere, Cylinder, Polyhedron, Rotate3, Transform3, Extrude,
                   ExtrudeM, ExtrudeOnEdgeOf, RotateExtrude, Shared3, Torus, Ellipsoid, BoxFrame, Link),
      Obj3,
      ℝ2,
      ℝ,
      fromℕtoℝ,
      fromℕ,
      toScaleFn,
      ℝ3 )

-- For handling extrusion of 2D shapes to 3D.
import {-# SOURCE #-} Graphics.Implicit.Primitives (getImplicit)

import Graphics.Implicit.MathUtil (rmax, rmaximum)

import Graphics.Implicit.ObjectUtil.GetImplicitShared (getImplicitShared)

default (ℝ)

-- Length similar to the opengl version, needed for some of the shape definitions
openglLength :: (Linear.Metric f, Num (f ℝ), Applicative f) => f ℝ -> ℝ
openglLength v = distance (abs v) $ pure 0

-- Component wise maximum. This is what the opengl language is doing, so we need
-- it for the function as defined by the blog above.
-- See "Maximum" http://15462.courses.cs.cmu.edu/fall2019/article/20
compMax :: ℝ3 -> ℝ3 -> ℝ3
compMax (V3 a1 b1 c1) (V3 a2 b2 c2) = V3 (max a1 a2) (max b1 b2) (max c1 c2)

-- Get a function that describes the surface of the object.
getImplicit3 :: ObjectContext -> SymbolicObj3 -> Obj3
-- Primitives
getImplicit3 ctx (Cube (V3 dx dy dz)) =
    \(V3 x y z) -> rmaximum (objectRounding ctx) [abs (x-dx/2) - dx/2, abs (y-dy/2) - dy/2, abs (z-dz/2) - dz/2]
getImplicit3 _ (Sphere r) =
    \(V3 x y z) -> sqrt (x*x + y*y + z*z) - r
getImplicit3 _ (Torus r1 r2) =  \(V3 x y z) -> let a = (sqrt (x**2 + y**2) - r1) in a**2 + z**2 - r2**2
getImplicit3 _ (Ellipsoid a b c) = \(V3 x y z) -> (x**2/a**2) + (y**2/b**2) + (z**2/c**2) - 1
getImplicit3 _ (Cylinder h r1 r2) = \(V3 x y z) ->
    let
        d = sqrt (x*x + y*y) - ((r2-r1)/h*z+r1)
        θ = atan2 (r2-r1) h
    in
        max (d * cos θ) (abs (z-h/2) - (h/2))
-- FIXME: Make Polyhedron correct by construction.
getImplicit3 _ (Polyhedron [] _) = error "Asked to find distance to an empty polygon. No points."
getImplicit3 _ (Polyhedron _ []) = error "Asked to find distance to an empty polygon. No tris."
getImplicit3 _ (Polyhedron points tris) = \(point) ->
  if insideMesh triangles point
  then negate $ minimum $ distancePointToTriangle point <$> triangles
  else          minimum $ distancePointToTriangle point <$> triangles
  where
    -- decompose our tris into triangles.
    triangles = findTriangle points <$> tris
    -- FIXME: make these indices correct by construction?
    findTriangle :: [V3 ℝ] -> (ℕ,ℕ,ℕ) -> (V3 ℝ, V3 ℝ, V3 ℝ)
    findTriangle virtices (i1,i2,i3)
      | outOfRange i1 = error $ "bad virtex index(out of range): " <> show i1 <> "\n"
      | outOfRange i2 = error $ "bad virtex index(out of range): " <> show i2 <> "\n"
      | outOfRange i3 = error $ "bad virtex index(out of range): " <> show i3 <> "\n"
      -- FIXME: there are many more degenerate forms of polyhedron possible here. move polyhedron to only holding a mesh?
      | otherwise = (genericIndex virtices i1, genericIndex virtices i2, genericIndex virtices i3)
        where
          -- FIXME: >=BASE-4.21: replace this with compareLength once debian stable ships 4.21.
          outOfRange :: ℕ -> Bool
          outOfRange v = v < 0 || length virtices < fromℕ v
getImplicit3 _ (BoxFrame b e) = \p' ->
    let p@(V3 px py pz) = abs p' - b
        V3 qx qy qz = abs (p + pure e) - pure e
        -- Splitting out bits from https://iquilezles.org/articles/distfunctions/
        -- to make it somewhat readable.
        -- These names don't mean anything, and are just for splitting up the code.
        x', y', z' :: ℝ
        x' = openglLength (compMax (V3 px qy qz) (pure 0)) + min (max px (max qy qz)) 0
        y' = openglLength (compMax (V3 qx py qz) (pure 0)) + min (max qx (max py qz)) 0
        z' = openglLength (compMax (V3 qx qy pz) (pure 0)) + min (max qx (max qy pz)) 0
    in min (min x' y') z'
getImplicit3 _ (Link le r1 r2) = \(V3 px py pz) ->
    let q = V3 px (max (abs py - le) 0) pz
    in openglLength (V2 (openglLength (q ^. _xy) - r1) (q ^. _z)) - r2
-- Simple transforms
getImplicit3 ctx (Rotate3 q symbObj) =
    getImplicit3 ctx symbObj . Linear.rotate (Linear.conjugate q)
getImplicit3 ctx (Transform3 m symbObj) =
    getImplicit3 ctx symbObj . Linear.normalizePoint . (Linear.inv44 m !*) . Linear.point
-- 2D Based
getImplicit3 ctx (Extrude h symbObj) =
    let
        obj = getImplicit symbObj
    in
        \(V3 x y z) -> rmax (objectRounding ctx) (obj (V2 x y)) (abs (z - h/2) - h/2)
getImplicit3 ctx (ExtrudeM twist scale translate symbObj height) =
    let
        r = objectRounding ctx
        obj = getImplicit symbObj
        height' (V2 x y) = case height of
            Left n -> n
            Right f -> f (V2 x y)
        -- FIXME: twist functions should have access to height, if height is allowed to vary.
        twistVal :: Either ℝ (ℝ -> ℝ) -> ℝ -> ℝ -> ℝ
        twistVal twist' z h =
          case twist' of
                   Left twval  -> if twval == 0
                                  then 0
                                  else twval * (z / h)
                   Right twfun -> twfun z
        translatePos :: Either ℝ2 (ℝ -> ℝ2) -> ℝ -> ℝ2 -> ℝ2
        translatePos trans z (V2 x y) = V2 (x - xTrans) (y - yTrans)
          where
            (V2 xTrans yTrans) = case trans of
                                 Left  tval -> tval
                                 Right tfun -> tfun z
        scaleVec :: ℝ -> ℝ2 -> ℝ2
        scaleVec z (V2 x y) = let (V2 sx sy) = toScaleFn scale z
                               in V2 (x / sx) (y / sy)
        rotateVec :: ℝ -> ℝ2 -> ℝ2
        rotateVec θ (V2 x y)
          | θ == 0    = V2 x y
          | otherwise = V2 (x*cos θ + y*sin θ) (y*cos θ - x*sin θ)
        k :: ℝ
        k = pi/180
    in
        \(V3 x y z) ->
          let
            h = height' $ V2 x y
            res = rmax r
                (obj
                 . rotateVec (-k*twistVal twist z h)
                 . scaleVec z
                 . translatePos translate z
                 $ V2 x y )
                (abs (z - h/2) - h/2)
          in
            res
getImplicit3 _ (ExtrudeOnEdgeOf symbObj1 symbObj2) =
    let
        obj1 = getImplicit symbObj1
        obj2 = getImplicit symbObj2
    in
        \(V3 x y z) -> obj1 $ V2 (obj2 (V2 x y)) z
getImplicit3 ctx (RotateExtrude totalRotation translate rotate symbObj) =
    let
        tau :: ℝ
        tau = 2 * pi
        obj = getImplicit symbObj

        is360m :: ℝ -> Bool
        is360m n = tau * fromInteger (round $ n / tau) /= n
        capped
             = is360m totalRotation
            || either ( /= pure 0) (\f -> f 0 /= f totalRotation) translate
            || either is360m (\f -> is360m (f 0 - f totalRotation)) rotate
        round' = objectRounding ctx
        translate' :: ℝ -> ℝ2
        translate' = Either.either
                (\(V2 a b) θ -> V2 (a*θ/totalRotation) (b*θ/totalRotation))
                id
                translate
        rotate' :: ℝ -> ℝ
        rotate' = Either.either
                (\t θ -> t*θ/totalRotation )
                id
                rotate
        twists = case rotate of
                   Left 0  -> True
                   _       -> False
    in
        \(V3 x y z) -> minimum $ do
            let
                r = sqrt $ x*x + y*y
                θ = atan2 y x
                ns :: [ℕ]
                ns =
                    if capped
                    then -- we will cap a different way, but want leeway to keep the function cont
                        [-1 .. ceiling $ (totalRotation / tau) + 1]
                    else
                        [0 .. floor $ (totalRotation - θ) / tau]
            n <- ns
            let
                θvirt = fromℕtoℝ n * tau + θ
                (V2 rshift zshift) = translate' θvirt
                twist = rotate' θvirt
                rz_pos = if twists
                        then let
                            (c,s) = (cos twist, sin twist)
                            (r',z') = (r-rshift, z-zshift)
                        in
                            V2 (c*r' - s*z') (c*z' + s*r')
                        else V2 (r - rshift) (z - zshift)
            pure $
              if capped
              then rmax round'
                    (abs (θvirt - (totalRotation / 2)) - (totalRotation / 2))
                    (obj rz_pos)
              else obj rz_pos
getImplicit3 ctx (Shared3 obj) = getImplicitShared ctx obj

-- | Check to see if a point is inside or outside of a mesh.
insideMesh :: [(V3 ℝ, V3 ℝ, V3 ℝ)] -> V3 ℝ -> Bool
insideMesh triangles point = odd $ length $ foundIntersection point unsafeSafeRay <$> triangles
  where
    -- our assumed safe ray. it's not really safe, but.. gotta start somewhere.
    unsafeSafeRay :: V3 ℝ
    unsafeSafeRay = Linear.normalize $ V3 (sqrt 2) (sqrt 3) (sqrt 5)
    foundIntersection :: V3 ℝ -> V3 ℝ -> (V3 ℝ, V3 ℝ, V3 ℝ) -> Bool
    foundIntersection source direction (v1, v2, v3)
      -- shouldn't happen, triangle is on the same plane as unsafeSafeRay
      | abs determinate <= 0 = False
      -- the intersection is not on the triangle (distance along vec12 out of range)
      | u <= 0 || u > 1      = False
      | v <= 0 || v > 1      = False
      | u + v > 1            = False
      | otherwise            = True
      where
        -- Our edge vectors. We have picked v1 to address the space by, for convenience.
        vec12 = v2 - v1
        vec13 = v3 - v1
        -- The normal of the plane formed by vec13 and our 'safe' vector. at 90 degree angles to both.
        norm13d = direction `cross` vec13
        -- The determinate. A volume. AKA, how close to parallel are the triangle, and the plane with normal norm13d.
        determinate = vec12 `dot` norm13d
        -- An edge vector in our 'safe' direction, from v1.
        vec1s = source - v1
        -- The distance along vec12 to find the intersection of a ray from source in direction direction, and the plane our triangle is on.
        u = (vec1s `dot` norm13d) / determinate
        -- The normal of the plane fromed by vec12 and vec1s.
        norm121s = vec1s `cross` vec12
        -- The distance along vec13 to find the intersertion of a ray from source in direction direction, and the plane our triangle is on.
        v = (direction `dot` norm121s) / determinate

-- With inspiration from: https://github.com/RenderKit/embree/blob/master/tutorials/common/math/closest_point.h
-- FIXME: Sensitive to really skinny triangles; detect these, and select a different 'v1'?.
distancePointToTriangle :: V3 ℝ -> (V3 ℝ,V3 ℝ,V3 ℝ) -> ℝ
distancePointToTriangle point (virtex1, virtex2, virtex3) = distance point closestPointToTriangleCenteredSorted
  where
    -- FIXME: Here are two precision error mitigation wrappers. Find out if they're needed.
    -- Reorder triangles such that we use the corner across from the longest side to address the space.
    closestPointToTriangleCenteredSorted :: V3 ℝ
    closestPointToTriangleCenteredSorted = closestPointToTriangleCentered adjustedTriangle
      where
        adjustedTriangle
          | abLength >= bcLength && abLength >= caLength = (virtex3, virtex1, virtex2)
          | abLength >= caLength                         = (virtex1, virtex2, virtex3)
          | otherwise                                    = (virtex2, virtex3, virtex1)
          where
            -- Really, using length-squared. don't have to abs it, don't have to sqrt it.
            abLength = (virtex2-virtex1) `dot` (virtex2-virtex1)
            bcLength = (virtex3-virtex2) `dot` (virtex3-virtex2)
            caLength = (virtex1-virtex3) `dot` (virtex1-virtex3)
    -- Force closestPointToTriangle to work at the origin
    closestPointToTriangleCentered :: (V3 ℝ,V3 ℝ,V3 ℝ) -> V3 ℝ
    closestPointToTriangleCentered (vir1, vir2, vir3) = originDistance + closestPointToTriangle adjustedTriangle adjustedPoint
      where
        originDistance = 1/3 *^ (vir1 + vir2 + vir3)
        adjustedTriangle = (vir1 - originDistance, vir2 - originDistance, vir3 - originDistance)
        adjustedPoint = point - originDistance
    closestPointToTriangle :: (V3 ℝ,V3 ℝ,V3 ℝ) -> V3 ℝ -> V3 ℝ
    closestPointToTriangle (v1, v2, v3) p
      -- Closest to the virtices
      | d1 <= 0 && d2 <=  0 = v1
      | d3 <= 0 && d4 <= d3 = v2
      | d5 <= 0 && d6 <= d5 = v3
      -- Closest to the edges
      | va <= 0 && d1 >=  0 && d3 <= 0 = v1 + (d1 / (d1 - d3)) *^ vec12
      | vb <= 0 && d2 >=  0 && d6 <= 0 = v1 + (d2 / (d2 - d6)) *^ vec13
      | vc <= 0 && dx >=  0 && dy >= 0 = v2 + (dx / (dx + dy)) *^ vec23
      -- On the triangle's surface
      | otherwise = (va / denom *^ v1) + (vb / denom *^ v2) + (vc / denom *^ v3)
      where
        -- The distance along edge12 and edge23, for segment V1 -> P when translated onto the triangle's plane.
        -- (P when translaned? Read: a line is drawn down to the plane the triangle is on, from p, to a point that is at a right angle with said line.)
        d1 = vec12 `dot` vec1p
        d2 = vec13 `dot` vec1p
        -- Our edge vectors. We have picked v1 to address the space by, for convenience.
        vec12 = v2 - v1
        vec13 = v3 - v1
        -- A segment between our point, and chosen virtex.
        vec1p =  p - v1
        -- Distance along edge12 and edge23, for segment V2 -> P when translated onto the triangle's plane.
        d3 = vec12 `dot` vec2p
        d4 = vec13 `dot` vec2p
        -- A segment between our point, and the second virtex.
        vec2p =  p - v2
        -- Distance along edge12 and edge23, for segment V3 -> P when translated onto the triangle's plane.
        d5 = vec12 `dot` vec3p
        d6 = vec13 `dot` vec3p
        -- A segment between our point, and the third virtex.
        vec3p =  p - v3
        -- An edge vector, along edge23.
        vec23 = v3 - v2
        -- The fractional denenominators.
        va = d1 * d4 - d3 * d2
        vb = d2 * d5 - d6 * d1
        vc = d3 * d6 - d5 * d4
        -- Two convienience values, to make the spacing on the formulas above work.
        dx = d4 - d3
        dy = d5 - d6
        -- The denominator.
        denom = va + vb + vc
