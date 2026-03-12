-- Implicit CAD. Copyright (C) 2011, Christopher Olah (chris@colah.ca)
-- Copyright 2015 2016, Mike MacHenry (mike.machenry@gmail.com)
-- Copyright 2014-2026, Julia Longtin (julia.longtin@gmail.com)
-- Released under the GNU AGPLV3+, see LICENSE

-- You see, what I thought I'd do is put a raytracer inside of a raytracer... what could go wrong...
-- With inspiration from: https://github.com/RenderKit/embree/blob/master/tutorials/common/math/closest_point.h

module Graphics.Implicit.TriUtil (
  angleAt,
  closestFeatureToTriangle,
  distancePointToTriangle,
  findTriangle,
  normOfTriangle,
  ClosestFeature(FeatFace,
                 FeatVertex1, FeatVertex2, FeatVertex3,
                 FeatEdge12,  FeatEdge13,  FeatEdge23),
  Tri
  ) where

import Prelude (acos, error, length, max, min, otherwise, show, (>), (<), (&&), (<=), (>=),($), (.), (/), (+), (-), (*), (==), (||), (<>), Bool, Eq)

import Graphics.Implicit.Definitions (
  fromℕ,
  ℝ,
  ℝ3,
  ℕ)

import Data.List (genericIndex)

import Linear (dot, distance)
import qualified Linear (normalize)

-- The cross product.
import Linear.V3 (cross)

-- Matrix times scalar.
import Linear.Vector ((*^))

type Tri = (ℕ,ℕ,ℕ)

type Triangle = (ℝ3, ℝ3, ℝ3)

-- The closest part of a triangle to a point.
data ClosestFeature = FeatVertex1 | FeatVertex2 | FeatVertex3 | FeatEdge12 | FeatEdge13 | FeatEdge23 | FeatFace
  deriving Eq

-- FIXME: Make these indices correct by construction?
findTriangle :: [ℝ3] -> Tri -> Triangle
findTriangle vertices (i1,i2,i3)
  | outOfRange i1 = error $ "bad vertex index(out of range): " <> show i1 <> "\n"
  | outOfRange i2 = error $ "bad vertex index(out of range): " <> show i2 <> "\n"
  | outOfRange i3 = error $ "bad vertex index(out of range): " <> show i3 <> "\n"
  -- FIXME: there are many more degenerate forms of polyhedron possible here. move polyhedron to only holding a mesh?
  | otherwise = (genericIndex vertices i1, genericIndex vertices i2, genericIndex vertices i3)
  where
    -- FIXME: >=BASE-4.21: replace this with compareLength once debian stable ships 4.21.
    outOfRange :: ℕ -> Bool
    outOfRange v = v < 0 || length vertices <= fromℕ v

normOfTriangle :: Triangle -> ℝ3
normOfTriangle (v1,v2,v3) = Linear.normalize $ (v2-v1) `cross` (v3-v1)

angleAt :: ℝ3 -> Triangle -> ℝ
angleAt vertex (v1,v2,v3)
  | vertex == v1 = acos $ clamp $ Linear.normalize (v2-v1) `dot` Linear.normalize (v3-v1)
  | vertex == v2 = acos $ clamp $ Linear.normalize (v1-v2) `dot` Linear.normalize (v3-v2)
  | vertex == v3 = acos $ clamp $ Linear.normalize (v1-v3) `dot` Linear.normalize (v2-v3)
  | otherwise = error $ "tried to get angleAt with a point not one of the vertexes: " <> show vertex <> "\n"
  where
    clamp :: ℝ -> ℝ
    clamp = max (-1) . min 1

distancePointToTriangle :: ℝ3 -> Triangle -> (ClosestFeature, ℝ)
distancePointToTriangle point (vertex1, vertex2, vertex3) = (adjustedFeature, distance point pointOnFeature)
  where
    (resFeature, pointOnFeature) = closestFeatureToTriangleCentered adjustedTriangle point
    -- First math precision transform: change which adressing system we use for the triangle, ensuring the far side is 'away' from the virtex we address from.
    adjustedFeature
      | adjustedTriangle == (vertex3, vertex1, vertex2) =
        case resFeature of
          FeatVertex1 -> FeatVertex3
          FeatVertex2 -> FeatVertex1
          FeatVertex3 -> FeatVertex2
          FeatEdge12  -> FeatEdge13
          FeatEdge13  -> FeatEdge23
          FeatEdge23  -> FeatEdge12
          FeatFace -> FeatFace
      | adjustedTriangle == (vertex2, vertex3, vertex1) =
        case resFeature of
          FeatVertex1 -> FeatVertex2
          FeatVertex2 -> FeatVertex3
          FeatVertex3 -> FeatVertex1
          FeatEdge12  -> FeatEdge23
          FeatEdge13  -> FeatEdge12
          FeatEdge23  -> FeatEdge13
          FeatFace -> FeatFace
      | otherwise = resFeature
    adjustedTriangle
      | abLength >= bcLength && abLength >= caLength = (vertex3, vertex1, vertex2)
      | abLength >= caLength                         = (vertex1, vertex2, vertex3)
      | otherwise                                    = (vertex2, vertex3, vertex1)
      where
        -- Really, using length-squared. don't have to abs it, don't have to sqrt it.
        abLength = (vertex2-vertex1) `dot` (vertex2-vertex1)
        bcLength = (vertex3-vertex2) `dot` (vertex3-vertex2)
        caLength = (vertex1-vertex3) `dot` (vertex1-vertex3)
    -- Second math precision transform: Force closestFeatureToTriangle to work near the origin by translating our query, and then translating the response.
    closestFeatureToTriangleCentered :: Triangle -> ℝ3 -> (ClosestFeature, ℝ3)
    closestFeatureToTriangleCentered (ver1, ver2, ver3) inpoint = (feature, originDistance + res)
      where
        (feature, res) = closestFeatureToTriangle translatedTriangle translatedPoint
        translatedTriangle = (ver1 - originDistance, ver2 - originDistance, ver3 - originDistance)
        translatedPoint = inpoint - originDistance
        originDistance = 1/3 *^ (ver1 + ver2 + ver3)

-- | Find the closest part of a triangle (edge, center, vertex) to a given point , along with the point on the closest part that is closest to the given point.
closestFeatureToTriangle :: Triangle -> ℝ3 -> (ClosestFeature, ℝ3)
closestFeatureToTriangle (v1, v2, v3) p
  -- Closest to the vertices
  | d1 <= 0 && d2 <=  0 = (FeatVertex1, v1)
  | d3 >= 0 && d4 <= d3 = (FeatVertex2, v2)
  | d6 >= 0 && d5 <= d6 = (FeatVertex3, v3)
  -- Nearest to the edges
  | va <= 0 && d1 > 0 && d3 <= 0 = (FeatEdge12, v1 + (d1 / (d1 - d3)) *^ vec12)
  | vb <= 0 && d2 > 0 && d6 <= 0 = (FeatEdge13, v1 + (d2 / (d2 - d6)) *^ vec13)
  | vc <= 0 && dx > 0 && dy  > 0 = (FeatEdge23, v2 + (dx / (dx + dy)) *^ vec23)
  -- Exactly on an edge, don't bother dividing by zero, please.
  | denom == 0 = (FeatFace, p)
  -- On the triangle's surface
  | otherwise = (FeatFace, v1 + v *^ vec12 + w *^ vec13)
  where
    -- The distance along edge12 and edge23, for segment V1 -> P when translated onto the triangle's plane.
    -- (P when translaned? Read: a line is drawn down to the plane the triangle is on, from p, to a point that is at a right angle with said line.)
    d1 = vec12 `dot` vec1p
    d2 = vec13 `dot` vec1p
    -- Our edge vectors. We have picked v1 to address the space by, for convenience.
    vec12 = v2 - v1
    vec13 = v3 - v1
    -- A segment between our point, and chosen vertex.
    vec1p =  p - v1
    -- Distance along edge12 and edge23, for segment V2 -> P when translated onto the triangle's plane.
    d3 = vec12 `dot` vec2p
    d4 = vec13 `dot` vec2p
    -- A segment between our point, and the second vertex.
    vec2p =  p - v2
    -- Distance along edge12 and edge23, for segment V3 -> P when translated onto the triangle's plane.
    d5 = vec12 `dot` vec3p
    d6 = vec13 `dot` vec3p
    -- A segment between our point, and the third vertex.
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
    -- barycentric results, where we actually intersect.
    v = vb / denom
    w = va / denom
