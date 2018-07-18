package viper.silver.plugin
object OuroborosHelper {
  def transformAndFold[B, A](toFold: Seq[B], initial: A, foldFunction: ((A,A)=> A), function: (B => A)): A ={
    toFold.toList match {
      case x :: Nil => function(x)
      case x :: xs => foldFunction(function(x), transformAndFold[B, A](xs, initial, foldFunction, function))
      case Nil =>
        initial
    }
  }

  def ourFold[A](toFold: Seq[A], initial: A, foldFunction: ((A,A)=> A)): A ={
    toFold.toList match {
      case x :: Nil => x
      case x :: xs =>
        foldFunction(x, ourFold[A](xs, initial, foldFunction))
      case Nil =>
        initial
    }
  }

}
