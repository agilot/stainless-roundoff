// HotSpots.standardRemapping adapted from Pinapse/giant (GNU General Public License v3.0)
// Source: https://github.com/Pinapse/giant/blob/04b79b7f2cc0934d81d9bcae47aa41880e134886/src/main/scala/net/psforever/zones/Zones.scala#L954
// Calls HotSpots.findClosestDivision (seed 185): https://github.com/Pinapse/giant/blob/04b79b7f2cc0934d81d9bcae47aa41880e134886/src/main/scala/net/psforever/zones/Zones.scala#L982
package net.psforever.zones

import stainless.annotation.*

// From net.psforever.types (src/main/scala/net/psforever/types/Vector3.scala)
final case class Vector3(x: Float, y: Float, z: Float)

// From net.psforever.objects.zones (src/main/scala/net/psforever/objects/zones/MapScale.scala)
final case class MapScale(width: Float, height: Float)

object Zones {
  object HotSpots {

    @roundoff
    def standardRemapping(scale: MapScale, longDivNum: Int, latDivNum: Int)(pos: Vector3): Vector3 = {
      require(2048.0f <= scale.width && scale.width <= 8192.0f)
      require(2048.0f <= scale.height && scale.height <= 8192.0f)
      require(scale.width == scale.height)
      require(80 <= longDivNum && longDivNum <= 80)
      require(80 <= latDivNum && latDivNum <= 80)
      require(0.0f <= pos.x && pos.x <= 8192.0f && pos.x <= scale.width)
      require(0.0f <= pos.y && pos.y <= 8192.0f && pos.y <= scale.height)
      Vector3(
        //x
        findClosestDivision(pos.x, scale.width, longDivNum.toFloat),
        //y
        findClosestDivision(pos.y, scale.height, latDivNum.toFloat),
        //z is always zero - maps are flat 2D planes
        0
      )
    }

    private def findClosestDivision(coordinate: Float, scale: Float, divisions: Float): Float = {
      require(2048.0f <= scale && scale <= 8192.0f)
      require(80.0f <= divisions && divisions <= 80.0f)
      val divLength: Float = scale / divisions
      if (coordinate >= scale - divLength) {
        scale - divLength
      } else if (coordinate >= divLength) {
        val sector: Float     = (coordinate * divisions / scale).toInt * divLength
        val nextSector: Float = sector + divLength
        if (coordinate - sector < nextSector - coordinate) {
          sector
        } else {
          nextSector
        }
      } else {
        divLength
      }
    }
  }
}
