// EntityLiving.heal adapted from Th3Falc0n/Terra-Infinita (GNU General Public License v2.0)
// Source: https://github.com/Th3Falc0n/Terra-Infinita/blob/76aa3da2a185d1dc19b086aa3d771e7c22fea6a5/terra/src/main/scala/com/dafttech/terra/game/world/entities/models/EntityLiving.scala#L59
package com.dafttech.terra.game.world.entities.models

import stainless.annotation.*

class EntityLiving(private val health: Float = 10) {
  private val maxHealth: Float = 10

  @roundoff
  def heal(health: Float): EntityLiving = {
    require(0.0f <= this.health && this.health <= 10.0f)
    require(-10.0f <= health && health <= 10.0f)
    var updated = this.health
    updated += health
    if (updated < 0) updated = 0
    if (updated > maxHealth) updated = maxHealth
    new EntityLiving(updated)
  }
}
