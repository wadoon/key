/*@ public normal_behaviour
  @   requires (\forall int x; (\forall int y; 0 <= x && x < y && y < a.length; a[x] <= a[y]));
  @   ensures ((\exists int x; 0 <= x && x < a.length; a[x] == v) ? a[\result] == v : \result == -1);
  @   // This is a comment inside JML!

      assignable \strictly_nothing;
      {*
        Multline comments!
      *}

  @*/

  int test_if_multiline_jml_is_interrupatable;
  /*@
    {*
   */
  int here_should_be_java_again;
