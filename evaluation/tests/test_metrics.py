import numpy as np

from fastmlfe2_eval.metrics import gradient_error, mse_error, sad_error


def _make_pair(*, h: int = 8, w: int = 8, c: int = 3):
    """Create a simple estimated/reference pair with known properties."""
    rng = np.random.default_rng(42)
    ref = rng.random((h, w, c))
    est = ref.copy()
    alpha = rng.random((h, w))
    mask = (alpha > 0) & (alpha < 1)
    return est, ref, alpha, mask


def test_sad_zero_for_identical():
    est, ref, alpha, mask = _make_pair()
    assert sad_error(est, ref, alpha, mask) == 0.0


def test_mse_zero_for_identical():
    est, ref, alpha, mask = _make_pair()
    assert mse_error(est, ref, alpha, mask) == 0.0


def test_gradient_error_zero_for_identical():
    est, ref, alpha, mask = _make_pair()
    assert gradient_error(est, ref, alpha, mask) == 0.0


def test_sad_positive_for_different():
    est, ref, alpha, mask = _make_pair()
    est = est + 0.1
    assert sad_error(est, ref, alpha, mask) > 0.0


def test_mse_positive_for_different():
    est, ref, alpha, mask = _make_pair()
    est = est + 0.1
    assert mse_error(est, ref, alpha, mask) > 0.0
