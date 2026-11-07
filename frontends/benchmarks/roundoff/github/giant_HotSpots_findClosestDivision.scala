// HotSpots.findClosestDivision adapted from Pinapse/giant (GNU General Public License v3.0)
// Source: https://github.com/Pinapse/giant/blob/04b79b7f2cc0934d81d9bcae47aa41880e134886/src/main/scala/net/psforever/zones/Zones.scala#L982
package net.psforever.zones

import stainless.annotation.*

object Zones {
  object HotSpots {

    @roundoff
    private def findClosestDivision(coordinate: Float, scale: Float, divisions: Float): Float = {
      require(0.0f <= coordinate && coordinate <= 8192.0f && coordinate <= scale)
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
