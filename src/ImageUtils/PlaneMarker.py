import cv2
import numpy as np


class ReferenceMarker:
    def getMarked(self, plane, coordinates):
        mask = np.zeros(plane.shape, dtype="uint8")
        cv2.rectangle(mask, (coordinates[0], coordinates[1]),
                      (coordinates[2], coordinates[3]), 255, -1)
        plane = cv2.bitwise_and(plane, mask)
        return plane
