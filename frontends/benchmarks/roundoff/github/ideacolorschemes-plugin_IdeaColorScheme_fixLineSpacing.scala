// IdeaColorScheme.fixLineSpacing adapted from iron9light/ideacolorschemes-plugin (Apache License 2.0)
// Source: https://github.com/iron9light/ideacolorschemes-plugin/blob/e81b804b91a635578ca3ba3df5d36194cc9f14c5/src/main/scala/com/ideacolorschemes/ideacolor/IdeaColorScheme.scala#L194
package com.ideacolorschemes.ideacolor

import stainless.annotation.*

class IdeaColorScheme {
  @roundoff
  def fixLineSpacing(lineSpacing: Float) = {
    require(0.0f <= lineSpacing && lineSpacing <= 3.0f)
    if (lineSpacing <= 0)
      1.0f
    else
      lineSpacing
  }
}
