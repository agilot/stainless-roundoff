// Vector2d.+ adapted from Th3Falc0n/Terra-Infinita (GNU General Public License v2.0)
// Source: https://github.com/Th3Falc0n/Terra-Infinita/blob/76aa3da2a185d1dc19b086aa3d771e7c22fea6a5/terra/src/main/scala/com/dafttech/terra/engine/vector/Vector2d.scala#L22
package com.dafttech.terra.engine.vector

import stainless.annotation.*
import stainless.lang.*

final case class Vector2d private(val x: Double,
                                  val y: Double) {

  @roundoff
  def +(x: Double, y: Double): Vector2d = {
    require(-100000.0 <= this.x && this.x <= 100000.0)
    require(-100000.0 <= this.y && this.y <= 100000.0)
    require(-1000.0 <= x && x <= 1000.0)
    require(-1000.0 <= y && y <= 1000.0)
    if (x == 0 && y == 0) this else Vector2d(this.x + x, this.y + y)
  }
}

object Vector2d {
  val Zero = new Vector2d(0, 0)
  val One = new Vector2d(1, 1)

  def apply(x: Double, y: Double): Vector2d = {
    require(x.isFinite && y.isFinite)
    if (x == 0 && y == 0) Zero
    else if (x == 1 && y == 1) One
    else new Vector2d(x, y)
  }
}
