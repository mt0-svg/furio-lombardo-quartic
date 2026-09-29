//! Finite field arithmetic, finite abelian groups, plane curves over finite fields and the Jacobian group law
//! of the quartic, used by the Mordell-Weil sieve (`code/jacobian-over-q/mw-sieve`) and the point counts
//! (`code/jacobian-over-q/lpoly`).

pub mod abgroup;
pub mod ff;
pub mod ffpoly;
pub mod jac_quartic;
pub mod plane_curve;
pub mod zeta;
