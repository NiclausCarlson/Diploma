import cv2
from skvideo.io import VideoWriter


def params_fetcher(video_path):
    cap = cv2.VideoCapture(video_path)
    ret, frame = cap.read()
    if ret:
        h, w, _ = frame.shape
        result = int(cap.get(cv2.CAP_PROP_FPS)), h, w
        cap.release()
        return result
    raise ValueError('Can\'t read video params')


class SimpleVideoWriter:
    def __init__(self, output_path, args):
        self._fps, self._height, self._width = args[0], args[1], args[2]
        self._out = VideoWriter(output_path, (self._height, self._width))
        self._out.open()

    def write_frame(self, frame):
        self._out.write(frame)

    def __del__(self):
        self._out.release()
