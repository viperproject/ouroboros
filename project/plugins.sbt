resolvers +=
  Resolver.url("bintray-mschwerhoff-sbt-plugins",
    url("https://dl.bintray.com/mschwerhoff/sbt-plugins/"))(Resolver.ivyStylePatterns)

addSbtPlugin("com.typesafe.sbteclipse" % "sbteclipse-plugin" % "5.1.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.2.0-M9")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.3")

addSbtPlugin("de.oakgrove" % "sbt-hgid" % "0.3")

addSbtPlugin("de.oakgrove" % "sbt-brand" % "0.3")