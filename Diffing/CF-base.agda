module Diffing.CF-base where

  open import CF
    public
  open import CF.Operations
    using (ar-dry; chv; μ-ar; Z; ZipperFor; ar; ch; fgt; μ-openv; plugv)
    public
  open import CF.Derivative
    using (φ-ar)
    public
  open import CF.Properties
    using (φ-ar-lemma; ar-std-lemma;
          fgt-plugv-lemma; ch-plugv-lemma;
          length-Z; ar-dry-0-lemma; fgt-ar-lemma;
         ◂-correct; Z-correct; plugv-correct)
    public
